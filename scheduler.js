/**
 * 教會季排班系統 - 核心引擎 (Scheduler Engine V17)
 * 依據 Logic_Analysis.md 實作：
 * 1. L=2 新朋友禁排邏輯 (每月 8-14 號)
 * 2. 嚴格的分數排序演算法 ([權重分, 歷史次數, 技能數量, 隨機數])
 * 3. 執行流程：執事 -> 跨堂預排 -> 家庭預排 -> 單堂填充 -> 補位 -> 最終 Refill
 * 4. FA 絕對同日同崗位，FB 絕對同日異崗位
 * 5. FA/FB 終極防落單替換機制 (依服事次數踢人)
 * 6. 完美平衡：配對預查機制 (Lookahead)，兼顧配對與次數平均。
 * 7. 【全新大升級】技能稀缺性保護與「弱者錨點」機制，保證多技能的高手優先被分配到高階崗位，不被家庭綁定浪費！
 */

const sessionsToSchedule = ['第一堂', '第二堂'];
const roleOrder = ['司會', 'PPT', '主餐', '收奉獻', '接待', '新朋友關懷'];

const ScheduleEngine = {
  formatDate(date) {
    const d = new Date(date);
    const yyyy = d.getFullYear();
    const mm = String(d.getMonth() + 1).padStart(2, '0');
    const dd = String(d.getDate()).padStart(2, '0');
    return `${yyyy}-${mm}-${dd}`;
  },

  getSundaysInQuarter(y, q) {
    const sundays = [];
    const startMonth = (q - 1) * 3;
    let d = new Date(y, startMonth, 1);
    while (d.getDay() !== 0) d.setDate(d.getDate() + 1);
    while (d.getMonth() >= startMonth && d.getMonth() < startMonth + 3) {
      sundays.push(new Date(d));
      d.setDate(d.getDate() + 7);
    }
    return sundays;
  },

  generate(params) {
    const {
      year = new Date().getFullYear(),
      quarter = 1,
      effectiveMembers = [],
      effectiveMemberPositions = [],
      dbData = {},
      roleSettings = {},
    } = params;

    const currentQuarterStr = `${year}-Q${quarter}`;

    // 防禦性修正：確保 newcomer_rule 與 dual_service_pref 都有完美從資料庫帶入
    effectiveMembers.forEach(m => {
        if (dbData.memberQuarterSettings) {
            const qs = dbData.memberQuarterSettings.find(s => s.member_id === m.id && s.quarter === currentQuarterStr);
            if (qs) {
                if (qs.newcomer_rule !== undefined && qs.newcomer_rule !== null) m.newcomer_rule = qs.newcomer_rule;
                if (qs.dual_service_pref !== undefined && qs.dual_service_pref !== null) m.dual_service_pref = qs.dual_service_pref;
            }
        }
    });

    const positions = params.positions || dbData.positions || [];
    const sundays = this.getSundaysInQuarter(year, quarter);

    const state = {
      draft: [],
      totalUsage: {},
      roleUsage: {},
      lastServedWeek: {},
      memberSkills: {},
      memberGroups: {}, 
    };

    this._prepareData(state, effectiveMembers, effectiveMemberPositions);

    const specialIds = {
      deacon: positions.find((p) => p?.name?.trim() === '執事輪值')?.id,
      mc: positions.find((p) => p?.name?.trim() === '司會')?.id,
      ppt: positions.find((p) => p?.name?.trim() === 'PPT')?.id,
      newcomer: positions.find((p) => p?.name?.trim() === '新朋友關懷')?.id,
    };

    sundays.forEach((sunday, weekIndex) => {
      const context = {
        sunday,
        weekIndex,
        dateStr: this.formatDate(sunday),
        dailyAssignments: {},
        availableSlots: this._createAvailableSlots(sunday, positions, roleSettings),
      };

      this._runSchedulingPipeline(state, context, effectiveMembers, specialIds);
    });

    this._applyVisualFlags(state.draft, effectiveMembers);
    this._sortFinalDraft(state.draft, effectiveMembers);

    return state.draft;
  },

  _prepareData(state, members, memberPositions) {
    members.forEach((m) => {
      state.totalUsage[m.id] = 0;
      state.roleUsage[m.id] = {};
      state.lastServedWeek[m.id] = -99;
      state.memberSkills[m.id] = new Set(
        memberPositions.filter((mp) => mp.member_id === m.id).map((mp) => mp.position_id)
      );
      if (m.group_id) {
          state.memberGroups[m.id] = m.group_id;
      }
    });
  },

  _createAvailableSlots(sunday, positions, roleSettings) {
    const slots = [];
    const isFirstSunday = sunday.getDate() <= 7;
    
    sessionsToSchedule.forEach((sess) => {
      positions.forEach((p) => {
        const roleName = p.name.trim();
        const needed = roleSettings[roleName] !== undefined ? roleSettings[roleName] : p.max_people || 0;
        if (needed <= 0) return;
        if (roleName === '主餐' && !isFirstSunday) return;
        
        slots.push({ session: sess, roleName: roleName, posId: p.id, needed: needed, assigned: [] });
      });
    });
    return slots;
  },

  _canAssign(m, slot, state, context, strictLevel = 0, skipFamilyCheck = false) {
    const { roleName, session, posId } = slot;
    
    if (['暫停服事', '安息季'].includes(m.availability_status)) return false;
    if (Array.isArray(m.unavailable_dates) && m.unavailable_dates.includes(context.dateStr)) return false;
    if (!state.memberSkills[m.id].has(posId)) return false;

    if (roleName === '執事輪值') {
      if ((state.roleUsage[m.id][posId] || 0) >= 4) return false;
    }

    if (roleName === '新朋友關懷') {
      const val = m.newcomer_rule;
      const isRule2or3 = (val === 2 || val === '2' || val === 3 || val === '3');
      if (isRule2or3 && context.sunday.getDate() >= 8 && context.sunday.getDate() <= 14) {
        return false;
      }
    }

    const dayShifts = state.draft.filter((d) => d.service_date === context.dateStr && d.member_id === m.id);
    const dayRoles = dayShifts.map(d => d._positionName);

    if (dayShifts.length >= 2) return false; 

    const dualPref = parseInt(m.dual_service_pref) || 0;

    if (roleName !== '執事輪值') {
        if (dayShifts.length === 1) {
            const firstShift = dayShifts[0];
            if (dualPref === 1) {
                if (firstShift.session === session) return false; 
                if (firstShift._positionName !== roleName) return false; 
            } else if (dualPref === 2) {
                if (firstShift.session === session) return false; 
                if (firstShift._positionName === roleName) return false; 
            } else {
                if (firstShift.session !== session) return false; 
                if (firstShift._positionName === roleName) return false; 
            }
        }

        if (dualPref === 0) {
            const leaderRoles = ['司會', 'PPT'];
            if (leaderRoles.includes(roleName) && dayShifts.length > 0) return false;
            if (dayRoles.some(r => leaderRoles.includes(r))) return false;
        }

        if (dayShifts.length === 0) {
            if (dualPref === 0 && m.preferred_session && m.preferred_session !== '皆可') {
                if (!m.preferred_session.includes(session.replace('堂', ''))) return false;
            }
        }
    }

    // 嚴格 FA/FB 檢查
    if (!skipFamilyCheck) {
        const myGroupId = state.memberGroups[m.id];
        if (myGroupId && (myGroupId.startsWith('FA') || myGroupId.startsWith('FB'))) {
            const assignedFamilyIds = Object.keys(context.dailyAssignments).filter(
                id => id !== m.id && state.memberGroups[id] === myGroupId
            );
            
            if (assignedFamilyIds.length > 0) {
                const familyRoles = new Set();
                assignedFamilyIds.forEach(fid => {
                    context.dailyAssignments[fid].forEach(r => familyRoles.add(r));
                });
                
                if (myGroupId.startsWith('FA')) {
                    if (!familyRoles.has(roleName)) return false;
                } else if (myGroupId.startsWith('FB')) {
                    if (familyRoles.has(roleName)) return false;
                }
            }
        }
    }

    return true;
  },

  _getScore(m, slot, state, context) {
    let weight = 0;

    if (['執事輪值', '司會'].includes(slot.roleName)) {
       const currentUsage = state.roleUsage[m.id][slot.posId] || 0;
       if (currentUsage === 0) weight -= 20000;
    }

    const dayRoles = context.dailyAssignments[m.id] || [];
    const comboRoles = ['接待', '收奉獻', '主餐', '新朋友關懷'];
    if (dayRoles.length === 1 && comboRoles.includes(slot.roleName) && comboRoles.includes(dayRoles[0])) {
       weight -= 5000;
    }

    if (state.lastServedWeek[m.id] === context.weekIndex - 1) {
       weight += 1000;
    }

    // 【核心優化】評分陣列加入 state.memberSkills[m.id].size (技能數量)
    // 排序權重：1. 絕對權重分 -> 2. 本季服事總次數 -> 3. 技能數量 (越少越優先) -> 4. 隨機
    // 確保只會「接待」的人優先填補通用崗位，把會「司會/PPT」的高手保留給高階崗位！
    return [
        weight, 
        state.totalUsage[m.id] || 0, 
        state.memberSkills[m.id].size, 
        Math.random()
    ];
  },

  _compareScore(scoreA, scoreB) {
    for (let i = 0; i < scoreA.length; i++) {
      if (scoreA[i] < scoreB[i]) return -1;
      if (scoreA[i] > scoreB[i]) return 1;
    }
    return 0;
  },

  _runSchedulingPipeline(state, context, members, specialIds) {
    this._assignDeacons(state, context, members, specialIds.deacon);

    // 第一階段正常填充：所有人都公平競爭，但在被選中時會觸發原子綁定
    sessionsToSchedule.forEach((sess) => {
      roleOrder.forEach(roleName => {
        const slots = context.availableSlots.filter(s => s.session === sess && s.roleName === roleName && s.needed > 0);
        slots.forEach(slot => {
             this._fillSlot(slot, members, state, context, 0);
        });
      });
    });

    this._enforceFO(state, context, members); 
    this._enforceFamily(state, context, members);

    // 第二階段補漏填充
    sessionsToSchedule.forEach((sess) => {
      roleOrder.forEach(roleName => {
        const slots = context.availableSlots.filter(s => s.session === sess && s.roleName === roleName && s.needed > 0);
        slots.forEach(slot => {
            this._fillSlot(slot, members, state, context, 1);
        });
      });
    });

    this._fillEmptyWarnings(state, context);
  },

  _fillSlot(slot, members, state, context, strictLevel) {
    let limit = 0;
    while (slot.needed > 0 && limit < 20) {
      const eligible = members.filter((m) => this._canAssign(m, slot, state, context, strictLevel));
      if (eligible.length === 0) break;

      // 進行公平計分排序 (此處的 _compareScore 已涵蓋「技能數量越少越優先」的保護機制)
      const scored = eligible.map(m => ({ m, score: this._getScore(m, slot, state, context) }));
      scored.sort((a, b) => this._compareScore(a.score, b.score));

      let successfullyAssigned = false;

      for (let candidate of scored) {
          const m = candidate.m;
          const gid = state.memberGroups[m.id];
          const dayShifts = state.draft.filter(d => d.service_date === context.dateStr && d.member_id === m.id);
          const isFirstMove = dayShifts.length === 0;

          const isFamily = gid && (gid.startsWith('FA') || gid.startsWith('FB'));
          const dualPref = parseInt(m.dual_service_pref) || 0;
          const isDual = dualPref === 1 || dualPref === 2;

          if (isFamily && isFirstMove) {
              if (this._tryAtomicFamilyAssign(m, slot, state, context, members, strictLevel)) {
                  successfullyAssigned = true;
                  break;
              }
          } else if (isDual && isFirstMove) {
              if (this._tryAtomicDualAssign(m, slot, state, context, strictLevel)) {
                  successfullyAssigned = true;
                  break;
              }
          } else {
              this._assign(m, slot, state, context);
              successfullyAssigned = true;
              break;
          }
      }

      if (!successfullyAssigned) break; 
      limit++;
    }
  },

  /**
   * 【原子級家庭綁定 + 弱者錨點機制】
   */
  _tryAtomicFamilyAssign(m0, slot0, state, context, members, strictLevel) {
      const gid = state.memberGroups[m0.id];
      const isFA = gid.startsWith('FA');
      const isFB = gid.startsWith('FB');

      // 【核心優化】取得家人並依據「技能數量」由少到多排序
      // 保證尋找位子時，技能受限的家人先被滿足，讓多技能的高手保留彈性去拿 高階崗位(如司會/PPT)
      const gMembers = members.filter(m => state.memberGroups[m.id] === gid)
                              .sort((a, b) => state.memberSkills[a.id].size - state.memberSkills[b.id].size);

      let allCanBePlaced = true;
      let plannedSlots = [{ member: m0, slot: slot0 }];
      let familyRoles = new Set([slot0.roleName]);

      for (let i = 0; i < gMembers.length; i++) {
          let m = gMembers[i];
          if (m.id === m0.id) continue;

          let foundSlotForM = false;
          let targetSessions = [slot0.session, slot0.session === '第一堂' ? '第二堂' : '第一堂'];

          for (let tSess of targetSessions) {
              // 這裡的 roleOrder 是從 司會 -> PPT -> 往下找
              // 因此多技能高手在這裡會自然被優先塞進高階稀缺崗位
              for (let tRole of roleOrder) {
                  if (isFA && !familyRoles.has(tRole)) continue;
                  if (isFB && familyRoles.has(tRole)) continue;

                  const slotN = context.availableSlots.find(s => s.session === tSess && s.roleName === tRole);
                  if (!slotN) continue;

                  const plannedCount = plannedSlots.filter(ps => ps.slot === slotN).length;
                  if (slotN.needed - plannedCount <= 0) continue;

                  if (this._canAssign(m, slotN, state, context, strictLevel, true)) {
                      plannedSlots.push({ member: m, slot: slotN });
                      familyRoles.add(tRole);
                      foundSlotForM = true;
                      break;
                  }
              }
              if (foundSlotForM) break;
          }

          if (!foundSlotForM) {
              allCanBePlaced = false;
              break; 
          }
      }

      if (allCanBePlaced) {
          for (let plan of plannedSlots) {
              this._assign(plan.member, plan.slot, state, context);
          }
          for (let plan of plannedSlots) {
              this._immediateFOFill(plan.member, state, context, members);
          }
          return true;
      }

      return false;
  },

  _tryAtomicDualAssign(m, slot, state, context, strictLevel) {
      const dualPref = parseInt(m.dual_service_pref) || 0;
      const otherSession = slot.session === '第一堂' ? '第二堂' : '第一堂';

      let targetSlot2 = null;
      if (dualPref === 1) {
          targetSlot2 = context.availableSlots.find(s => s.session === otherSession && s.roleName === slot.roleName && s.needed > 0 && this._canAssign(m, s, state, context, strictLevel, true));
      } else if (dualPref === 2) {
          targetSlot2 = context.availableSlots.find(s => s.session === otherSession && s.roleName !== slot.roleName && s.needed > 0 && this._canAssign(m, s, state, context, strictLevel, true));
      }

      if (targetSlot2) {
          this._assign(m, slot, state, context);
          this._assign(m, targetSlot2, state, context);
          return true;
      }
      return false; 
  },

  _immediateFOFill(baseMember, state, context, members) {
      const pref = parseInt(baseMember.dual_service_pref) || 0;
      if (pref !== 1 && pref !== 2) return;

      const dayShifts = state.draft.filter(d => d.service_date === context.dateStr && d.member_id === baseMember.id);
      if (dayShifts.length >= 2 || dayShifts.some(s => s._positionName === '執事輪值')) return;

      const currentShift = dayShifts[0];
      if (!currentShift) return;

      const targetSession = currentShift.session === '第一堂' ? '第二堂' : '第一堂';
      const targetSlots = context.availableSlots.filter(s => s.session === targetSession && s.needed > 0);

      let targetSlot = null;
      if (pref === 1) targetSlot = targetSlots.find(s => s.roleName === currentShift._positionName && this._canAssign(baseMember, s, state, context, 0, true));
      else if (pref === 2) targetSlot = targetSlots.find(s => s.roleName !== currentShift._positionName && this._canAssign(baseMember, s, state, context, 0, true));

      if (targetSlot) {
          this._assign(baseMember, targetSlot, state, context);
      }
  },

  _assignDeacons(state, context, members, deaconId) {
    if (!deaconId) return;
    const slots = context.availableSlots.filter((s) => s.posId === deaconId);
    if (slots.length === 0) return;
    
    let limit = 0;
    while (slots.some(s => s.needed > 0) && limit < 10) {
      const eligible = members.filter((m) => {
        const currentUsage = state.roleUsage[m.id]?.[deaconId] || 0;
        const neededSlots = slots.filter(s => s.needed > 0);
        if (currentUsage + neededSlots.length > 4) return false; 
        
        return neededSlots.every(s => this._canAssign(m, s, state, context, 0, true));
      });
      
      if (eligible.length === 0) break;
      
      const scored = eligible.map(m => ({ m, score: this._getScore(m, slots[0], state, context) }));
      scored.sort((a, b) => this._compareScore(a.score, b.score));
      const best = scored[0].m;
      
      slots.filter(s => s.needed > 0).forEach(s => this._assign(best, s, state, context));
      limit++;
    }
  },

  _enforceFO(state, context, members) {
    const todayShifts = state.draft.filter(d => d.service_date === context.dateStr);
    const assignedIds = [...new Set(todayShifts.map(d => d.member_id))];

    assignedIds.forEach(mId => {
       const m = members.find(x => x.id === mId);
       if (!m) return;
       const pref = parseInt(m.dual_service_pref);
       if (pref !== 1 && pref !== 2) return; 

       const myShifts = todayShifts.filter(d => d.member_id === m.id);
       if (myShifts.length >= 2 || myShifts.some(s => s._positionName === '執事輪值')) return;

       const currentShift = myShifts[0];
       const targetSession = currentShift.session === '第一堂' ? '第二堂' : '第一堂';
       const targetSlots = context.availableSlots.filter(s => s.session === targetSession && s.needed > 0);

       let targetSlot = null;
       if (pref === 1) targetSlot = targetSlots.find(s => s.roleName === currentShift._positionName && this._canAssign(m, s, state, context, 0, true));
       else if (pref === 2) targetSlot = targetSlots.find(s => s.roleName !== currentShift._positionName && this._canAssign(m, s, state, context, 0, true));

       if (targetSlot) {
         this._assign(m, targetSlot, state, context);
       }
    });
  },

  _enforceFamily(state, context, members) {
    const groups = {};
    members.forEach(m => {
      if (m.group_id && (m.group_id.startsWith('FA') || m.group_id.startsWith('FB'))) {
        if (!groups[m.group_id]) groups[m.group_id] = [];
        groups[m.group_id].push(m);
      }
    });

    const sortedGroupIds = Object.keys(groups).sort((a, b) => {
        const avgA = groups[a].reduce((s, m) => s + (state.totalUsage[m.id] || 0), 0) / groups[a].length;
        const avgB = groups[b].reduce((s, m) => s + (state.totalUsage[m.id] || 0), 0) / groups[b].length;
        return avgA - avgB;
    });

    sortedGroupIds.forEach(gid => {
      const gMembers = groups[gid];
      if (gMembers.length < 2) return;

      const assignedMembers = gMembers.filter(m => context.dailyAssignments[m.id]);
      const unassignedMembers = gMembers.filter(m => !context.dailyAssignments[m.id]);

      if (assignedMembers.length > 0 && unassignedMembers.length > 0) {
         const targetSession = state.draft.find(d => d.service_date === context.dateStr && d.member_id === assignedMembers[0].id)?.session;
         if (!targetSession) return;

         unassignedMembers.sort((a, b) => (state.totalUsage[a.id] || 0) - (state.totalUsage[b.id] || 0));

         unassignedMembers.forEach(unM => {
            let assigned = false;
            
            const targetSlots = context.availableSlots.filter(s => s.session === targetSession && s.needed > 0);
            for (let s of targetSlots) {
               if (this._canAssign(unM, s, state, context, 0, true)) {
                  this._assign(unM, s, state, context);
                  assigned = true;
                  break;
               }
            }

            if (!assigned) {
                const otherSlots = context.availableSlots.filter(s => s.session !== targetSession && s.needed > 0);
                for (let s of otherSlots) {
                   if (this._canAssign(unM, s, state, context, 0, true)) {
                      this._assign(unM, s, state, context);
                      assigned = true;
                      break;
                   }
                }
            }

            if (!assigned) {
                this._forceSwapForFamily(unM, assignedMembers[0], state, context, members);
            }
         });
      }
    });
  },

  _forceSwapForFamily(unM, baseMember, state, context, members) {
      const todayShifts = state.draft.filter(d => 
          d.service_date === context.dateStr && 
          !d.is_empty && 
          d.member_id !== unM.id && 
          d.member_id !== baseMember.id
      );
      
      let bestSwap = null;
      let bestScore = -9999;

      for (let shift of todayShifts) {
          if (shift._positionName === '執事輪值') continue;

          const mockSlot = { roleName: shift._positionName, session: shift.session, posId: shift.position_id };
          if (!this._canAssign(unM, mockSlot, state, context, 0, true)) continue;

          const victim = members.find(m => m.id === shift.member_id);
          if (!victim) continue;

          const victimGroupId = state.memberGroups[victim.id];
          if (victimGroupId && (victimGroupId.startsWith('FA') || victimGroupId.startsWith('FB'))) continue;

          const victimUsage = state.totalUsage[victim.id] || 0;
          const unMUsage = state.totalUsage[unM.id] || 0;
          const score = victimUsage - unMUsage;

          if (score > bestScore) {
              bestScore = score;
              bestSwap = { shift, victim, mockSlot };
          }
      }

      if (bestSwap) {
          this._replaceAssignment(unM, bestSwap.victim.id, bestSwap.shift.temp_id, bestSwap.mockSlot, state, context);
      }
  },

  _replaceAssignment(newMember, oldMemberId, targetTempId, slotInfo, state, context) {
      const draftIdx = state.draft.findIndex(d => d.temp_id === targetTempId);
      if (draftIdx === -1) return;

      state.totalUsage[oldMemberId] = Math.max(0, state.totalUsage[oldMemberId] - 1);
      if (state.roleUsage[oldMemberId][slotInfo.posId]) {
          state.roleUsage[oldMemberId][slotInfo.posId]--;
      }
      const dailyIdx = context.dailyAssignments[oldMemberId].indexOf(slotInfo.roleName);
      if (dailyIdx > -1) context.dailyAssignments[oldMemberId].splice(dailyIdx, 1);

      state.totalUsage[newMember.id] = (state.totalUsage[newMember.id] || 0) + 1;
      state.roleUsage[newMember.id][slotInfo.posId] = (state.roleUsage[newMember.id][slotInfo.posId] || 0) + 1;
      state.lastServedWeek[newMember.id] = context.weekIndex;
      if (!context.dailyAssignments[newMember.id]) context.dailyAssignments[newMember.id] = [];
      context.dailyAssignments[newMember.id].push(slotInfo.roleName);

      state.draft[draftIdx].member_id = newMember.id;
      state.draft[draftIdx]._memberName = newMember.name;
      state.draft[draftIdx].is_emergency = 2; 
  },

  _assign(m, slot, state, context, isEmergency = 0) {
    slot.assigned.push(m);
    slot.needed--;
    state.totalUsage[m.id]++;
    state.roleUsage[m.id][slot.posId] = (state.roleUsage[m.id][slot.posId] || 0) + 1;
    state.lastServedWeek[m.id] = context.weekIndex;
    
    if (!context.dailyAssignments[m.id]) context.dailyAssignments[m.id] = [];
    context.dailyAssignments[m.id].push(slot.roleName);

    state.draft.push({
      temp_id: `T_${context.dateStr}_${slot.session}_${slot.posId}_${Math.random()}`,
      service_date: context.dateStr, 
      session: slot.session, 
      member_id: m.id, 
      position_id: slot.posId,
      _memberName: m.name, 
      _positionName: slot.roleName, 
      is_emergency: isEmergency
    });
  },

  _fillEmptyWarnings(state, context) {
    context.availableSlots.forEach((slot) => {
      while (slot.needed > 0) {
        state.draft.push({
          temp_id: `EMPTY_${context.dateStr}_${slot.session}_${slot.posId}_${Math.random()}`,
          service_date: context.dateStr, 
          session: slot.session, 
          member_id: 'EMPTY_SLOT', 
          position_id: slot.posId,
          _memberName: '⚠️ 需手動指派', 
          _positionName: slot.roleName, 
          is_empty: true
        });
        slot.needed--;
      }
    });
  },

  _applyVisualFlags(draft, members) {
    const memberGroups = {};
    members.forEach(m => {
      if (m.group_id) memberGroups[m.id] = m.group_id;
    });

    const shiftsByDate = {};
    draft.forEach(d => {
      if (d.is_empty) return;
      if (!shiftsByDate[d.service_date]) shiftsByDate[d.service_date] = [];
      shiftsByDate[d.service_date].push(d);
    });

    Object.values(shiftsByDate).forEach(dayShifts => {
      const freq = {};
      const groupFreq = {};

      dayShifts.forEach(d => {
        freq[d.member_id] = (freq[d.member_id] || 0) + 1;
        
        const gid = memberGroups[d.member_id];
        if (gid && (gid.startsWith('FA') || gid.startsWith('FB'))) {
          if (!groupFreq[gid]) groupFreq[gid] = new Set();
          groupFreq[gid].add(d.member_id);
        }
      });

      dayShifts.forEach(d => {
        if (freq[d.member_id] >= 2) {
          d.is_duplicate = true;
        }

        const gid = memberGroups[d.member_id];
        if (gid && groupFreq[gid] && groupFreq[gid].size < 2) {
          d.is_lonely_family = true;
        }
      });
    });
  },

  _sortFinalDraft(draft, members) {
    const getRule = (m) => {
        if (!m || m.newcomer_rule == null) return 0;
        const val = m.newcomer_rule;
        if (val === 1 || val === '1') return 1;
        if (val === 2 || val === '2') return 2;
        if (val === 3 || val === '3') return 3;
        return 0;
    };

    draft.sort((a, b) => {
      if (a.service_date !== b.service_date) return a.service_date.localeCompare(b.service_date);
      if (a.session !== b.session) return a.session === '第一堂' ? -1 : 1;
      if (a._positionName !== b._positionName) return a._positionName.localeCompare(b._positionName);

      if (a._positionName === '新朋友關懷') {
         const memA = members.find(m => m.id === a.member_id);
         const memB = members.find(m => m.id === b.member_id);
         
         const ruleA = getRule(memA);
         const ruleB = getRule(memB);
         
         const prioA = (ruleA === 1 || ruleA === 3) ? 1 : 0;
         const prioB = (ruleB === 1 || ruleB === 3) ? 1 : 0;
         
         if (prioA !== prioB) return prioB - prioA; 

         if (a.is_empty !== b.is_empty) return a.is_empty ? 1 : -1;
         if (!a.is_empty && !b.is_empty) return a._memberName.localeCompare(b._memberName);
      }

      if (a.is_empty !== b.is_empty) return a.is_empty ? 1 : -1;

      return 0;
    });
  },
};

if (typeof window !== 'undefined') {
  window.ScheduleEngine = ScheduleEngine;
} else if (typeof module !== 'undefined') {
  module.exports = ScheduleEngine;
}
