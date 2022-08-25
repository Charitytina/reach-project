// Automatically generated with Reach 0.1.11 (27cb9643)
/* eslint-disable */
export const _version = '0.1.11';
export const _versionHash = '0.1.11 (27cb9643)';
export const _backendVersion = 19;

export function getExports(s) {
  const stdlib = s.reachStdlib;
  return {
    };
  };
export function _getEvents(s) {
  const stdlib = s.reachStdlib;
  return {
    };
  };
export function _getViews(s, viewlib) {
  const stdlib = s.reachStdlib;
  const ctc0 = stdlib.T_Address;
  const ctc1 = stdlib.T_UInt;
  const ctc2 = stdlib.T_Digest;
  
  return {
    infos: {
      },
    views: {
      1: [ctc0, ctc1, ctc1, ctc1, ctc1],
      5: [ctc0, ctc1, ctc1, ctc0, ctc1, ctc1],
      6: [ctc0, ctc1, ctc1, ctc0, ctc1, ctc1, ctc2, ctc1],
      8: [ctc0, ctc1, ctc1, ctc0, ctc1, ctc1, ctc2, ctc1, ctc1]
      }
    };
  
  };
export function _getMaps(s) {
  const stdlib = s.reachStdlib;
  const ctc0 = stdlib.T_Tuple([]);
  return {
    mapDataTy: ctc0
    };
  };
export async function A(ctcTop, interact) {
  if (typeof(ctcTop) !== 'object' || ctcTop._initialize === undefined) {
    return Promise.reject(new Error(`The backend for A expects to receive a contract as its first argument.`));}
  if (typeof(interact) !== 'object') {
    return Promise.reject(new Error(`The backend for A expects to receive an interact object as its second argument.`));}
  const ctc = ctcTop._initialize();
  const stdlib = ctc.stdlib;
  const ctc0 = stdlib.T_UInt;
  const ctc1 = stdlib.T_Tuple([ctc0, ctc0]);
  const ctc2 = stdlib.T_Digest;
  const ctc3 = stdlib.T_Null;
  const ctc4 = stdlib.T_Address;
  
  
  const v243 = stdlib.protect(ctc0, interact.deadline, 'for A\'s interact field deadline');
  const v244 = stdlib.protect(ctc0, interact.wager, 'for A\'s interact field wager');
  
  const v247 = stdlib.protect(ctc0, await interact.getRandomNumber(), {
    at: './index.rsh:55:56:application',
    fs: ['at ./index.rsh:53:9:application call to [unknown function] (defined at: ./index.rsh:53:13:function exp)'],
    msg: 'getRandomNumber',
    who: 'A'
    });
  
  const txn1 = await (ctc.sendrecv({
    args: [v244, v247, v243],
    evt_cnt: 3,
    funcNum: 0,
    lct: stdlib.checkedBigNumberify('./index.rsh:58:5:dot', stdlib.UInt_max, '0'),
    onlyIf: true,
    out_tys: [ctc0, ctc0, ctc0],
    pay: [v244, []],
    sim_p: (async (txn1) => {
      const sim_r = { txns: [], mapRefs: [], maps: [] };
      let sim_txn_ctr = stdlib.UInt_max;
      const getSimTokCtr = () => { sim_txn_ctr = sim_txn_ctr.sub(1); return sim_txn_ctr; };
      
      
      const {data: [v249, v250, v251], secs: v253, time: v252, didSend: v33, from: v248 } = txn1;
      
      sim_r.txns.push({
        amt: v249,
        kind: 'to',
        tok: undefined /* Nothing */
        });
      const v262 = stdlib.safeAdd(v252, v251);
      sim_r.isHalt = false;
      
      return sim_r;
      }),
    soloSend: true,
    timeoutAt: undefined /* mto */,
    tys: [ctc0, ctc0, ctc0],
    waitIfNotPresent: false
    }));
  const {data: [v249, v250, v251], secs: v253, time: v252, didSend: v33, from: v248 } = txn1;
  ;
  const v262 = stdlib.safeAdd(v252, v251);
  const txn2 = await (ctc.recv({
    didSend: false,
    evt_cnt: 1,
    funcNum: 1,
    out_tys: [ctc0],
    timeoutAt: ['time', v262],
    waitIfNotPresent: false
    }));
  if (txn2.didTimeout) {
    const txn3 = await (ctc.sendrecv({
      args: [v248, v249, v250, v251, v262],
      evt_cnt: 0,
      funcNum: 2,
      lct: v252,
      onlyIf: true,
      out_tys: [],
      pay: [stdlib.checkedBigNumberify('reach standard library:197:11:decimal', stdlib.UInt_max, '0'), []],
      sim_p: (async (txn3) => {
        const sim_r = { txns: [], mapRefs: [], maps: [] };
        let sim_txn_ctr = stdlib.UInt_max;
        const getSimTokCtr = () => { sim_txn_ctr = sim_txn_ctr.sub(1); return sim_txn_ctr; };
        
        
        const {data: [], secs: v404, time: v403, didSend: v209, from: v402 } = txn3;
        
        ;
        sim_r.txns.push({
          kind: 'from',
          to: v248,
          tok: undefined /* Nothing */
          });
        sim_r.txns.push({
          kind: 'halt',
          tok: undefined /* Nothing */
          })
        sim_r.isHalt = true;
        
        return sim_r;
        }),
      soloSend: false,
      timeoutAt: undefined /* mto */,
      tys: [ctc4, ctc0, ctc0, ctc0, ctc0],
      waitIfNotPresent: false
      }));
    const {data: [], secs: v404, time: v403, didSend: v209, from: v402 } = txn3;
    ;
    ;
    stdlib.protect(ctc3, await interact.informTimeout(), {
      at: './index.rsh:50:29:application',
      fs: ['at ./index.rsh:49:9:application call to [unknown function] (defined at: ./index.rsh:49:21:function exp)', 'at reach standard library:200:8:application call to "after" (defined at: ./index.rsh:48:28:function exp)', 'at ./index.rsh:65:78:application call to "closeTo" (defined at: reach standard library:195:8:function exp)'],
      msg: 'informTimeout',
      who: 'A'
      });
    
    return;
    
    }
  else {
    const {data: [v268], secs: v270, time: v269, didSend: v44, from: v267 } = txn2;
    const v272 = stdlib.safeAdd(v249, v249);
    ;
    const v273 = stdlib.safeAdd(v268, v250);
    const v274 = stdlib.safeDiv(v273, stdlib.checkedBigNumberify('./index.rsh:67:31:decimal', stdlib.UInt_max, '2'));
    let v275 = stdlib.checkedBigNumberify('./index.rsh:makeEnum', stdlib.UInt_max, '1');
    let v276 = v269;
    let v283 = v272;
    
    while (await (async () => {
      const v291 = stdlib.eq(v275, stdlib.checkedBigNumberify('./index.rsh:makeEnum', stdlib.UInt_max, '1'));
      
      return v291;})()) {
      const v294 = stdlib.protect(ctc0, await interact.getGuess(), {
        at: './index.rsh:74:38:application',
        fs: ['at ./index.rsh:73:9:application call to [unknown function] (defined at: ./index.rsh:73:13:function exp)'],
        msg: 'getGuess',
        who: 'A'
        });
      const v295 = stdlib.protect(ctc0, await interact.random(), {
        at: 'reach standard library:64:31:application',
        fs: ['at ./index.rsh:75:46:application call to "makeCommitment" (defined at: reach standard library:63:8:function exp)', 'at ./index.rsh:73:9:application call to [unknown function] (defined at: ./index.rsh:73:13:function exp)'],
        msg: 'random',
        who: 'A'
        });
      const v296 = stdlib.digest(ctc1, [v295, v294]);
      
      const txn3 = await (ctc.sendrecv({
        args: [v248, v249, v251, v267, v274, v283, v296],
        evt_cnt: 1,
        funcNum: 4,
        lct: v276,
        onlyIf: true,
        out_tys: [ctc2],
        pay: [stdlib.checkedBigNumberify('./index.rsh:78:5:decimal', stdlib.UInt_max, '0'), []],
        sim_p: (async (txn3) => {
          const sim_r = { txns: [], mapRefs: [], maps: [] };
          let sim_txn_ctr = stdlib.UInt_max;
          const getSimTokCtr = () => { sim_txn_ctr = sim_txn_ctr.sub(1); return sim_txn_ctr; };
          
          
          const {data: [v299], secs: v301, time: v300, didSend: v72, from: v298 } = txn3;
          
          ;
          const v309 = stdlib.safeAdd(v300, v251);
          sim_r.isHalt = false;
          
          return sim_r;
          }),
        soloSend: true,
        timeoutAt: undefined /* mto */,
        tys: [ctc4, ctc0, ctc0, ctc4, ctc0, ctc0, ctc2],
        waitIfNotPresent: false
        }));
      const {data: [v299], secs: v301, time: v300, didSend: v72, from: v298 } = txn3;
      ;
      const v302 = stdlib.addressEq(v248, v298);
      stdlib.assert(v302, {
        at: './index.rsh:78:5:dot',
        fs: [],
        msg: 'sender correct',
        who: 'A'
        });
      const v309 = stdlib.safeAdd(v300, v251);
      const txn4 = await (ctc.recv({
        didSend: false,
        evt_cnt: 1,
        funcNum: 5,
        out_tys: [ctc0],
        timeoutAt: ['time', v309],
        waitIfNotPresent: false
        }));
      if (txn4.didTimeout) {
        const txn5 = await (ctc.sendrecv({
          args: [v248, v249, v251, v267, v274, v283, v299, v309],
          evt_cnt: 0,
          funcNum: 6,
          lct: v300,
          onlyIf: true,
          out_tys: [],
          pay: [stdlib.checkedBigNumberify('reach standard library:197:11:decimal', stdlib.UInt_max, '0'), []],
          sim_p: (async (txn5) => {
            const sim_r = { txns: [], mapRefs: [], maps: [] };
            let sim_txn_ctr = stdlib.UInt_max;
            const getSimTokCtr = () => { sim_txn_ctr = sim_txn_ctr.sub(1); return sim_txn_ctr; };
            
            
            const {data: [], secs: v361, time: v360, didSend: v153, from: v359 } = txn5;
            
            ;
            sim_r.txns.push({
              kind: 'from',
              to: v248,
              tok: undefined /* Nothing */
              });
            sim_r.txns.push({
              kind: 'halt',
              tok: undefined /* Nothing */
              })
            sim_r.isHalt = true;
            
            return sim_r;
            }),
          soloSend: false,
          timeoutAt: undefined /* mto */,
          tys: [ctc4, ctc0, ctc0, ctc4, ctc0, ctc0, ctc2, ctc0],
          waitIfNotPresent: false
          }));
        const {data: [], secs: v361, time: v360, didSend: v153, from: v359 } = txn5;
        ;
        const v362 = stdlib.addressEq(v248, v359);
        const v363 = stdlib.addressEq(v267, v359);
        const v364 = v362 ? true : v363;
        stdlib.assert(v364, {
          at: 'reach standard library:197:11:dot',
          fs: ['at ./index.rsh:85:66:application call to "closeTo" (defined at: reach standard library:195:8:function exp)'],
          msg: 'sender correct',
          who: 'A'
          });
        ;
        stdlib.protect(ctc3, await interact.informTimeout(), {
          at: './index.rsh:50:29:application',
          fs: ['at ./index.rsh:49:9:application call to [unknown function] (defined at: ./index.rsh:49:21:function exp)', 'at reach standard library:200:8:application call to "after" (defined at: ./index.rsh:48:28:function exp)', 'at ./index.rsh:85:66:application call to "closeTo" (defined at: reach standard library:195:8:function exp)'],
          msg: 'informTimeout',
          who: 'A'
          });
        
        return;
        
        }
      else {
        const {data: [v315], secs: v317, time: v316, didSend: v82, from: v314 } = txn4;
        ;
        const v318 = stdlib.addressEq(v267, v314);
        stdlib.assert(v318, {
          at: './index.rsh:85:5:dot',
          fs: [],
          msg: 'sender correct',
          who: 'A'
          });
        const v325 = stdlib.safeAdd(v316, v251);
        const txn5 = await (ctc.sendrecv({
          args: [v248, v249, v251, v267, v274, v283, v299, v315, v325, v295, v294],
          evt_cnt: 2,
          funcNum: 7,
          lct: v316,
          onlyIf: true,
          out_tys: [ctc0, ctc0],
          pay: [stdlib.checkedBigNumberify('./index.rsh:91:5:decimal', stdlib.UInt_max, '0'), []],
          sim_p: (async (txn5) => {
            const sim_r = { txns: [], mapRefs: [], maps: [] };
            let sim_txn_ctr = stdlib.UInt_max;
            const getSimTokCtr = () => { sim_txn_ctr = sim_txn_ctr.sub(1); return sim_txn_ctr; };
            
            
            const {data: [v330, v331], secs: v333, time: v332, didSend: v92, from: v329 } = txn5;
            
            ;
            let v337;
            const v338 = stdlib.eq(v315, v331);
            if (v338) {
              v337 = stdlib.checkedBigNumberify('./index.rsh:8:16:decimal', stdlib.UInt_max, '1');
              }
            else {
              const v339 = stdlib.eq(v315, v274);
              if (v339) {
                v337 = stdlib.checkedBigNumberify('./index.rsh:12:17:decimal', stdlib.UInt_max, '0');
                }
              else {
                const v340 = stdlib.eq(v331, v274);
                if (v340) {
                  v337 = stdlib.checkedBigNumberify('./index.rsh:16:17:decimal', stdlib.UInt_max, '2');
                  }
                else {
                  v337 = stdlib.checkedBigNumberify('./index.rsh:19:16:decimal', stdlib.UInt_max, '1');
                  }
                }
              }
            const cv275 = v337;
            const cv276 = v332;
            const cv283 = v283;
            
            await (async () => {
              const v275 = cv275;
              const v276 = cv276;
              const v283 = cv283;
              
              if (await (async () => {
                const v291 = stdlib.eq(v275, stdlib.checkedBigNumberify('./index.rsh:makeEnum', stdlib.UInt_max, '1'));
                
                return v291;})()) {
                sim_r.isHalt = false;
                }
              else {
                const v377 = stdlib.eq(v275, stdlib.checkedBigNumberify('./index.rsh:97:14:decimal', stdlib.UInt_max, '2'));
                const v378 = stdlib.eq(v275, stdlib.checkedBigNumberify('./index.rsh:98:14:decimal', stdlib.UInt_max, '0'));
                const v379 = [stdlib.checkedBigNumberify('<builtin>', stdlib.UInt_max, '0'), stdlib.checkedBigNumberify('<builtin>', stdlib.UInt_max, '2')];
                const v380 = [stdlib.checkedBigNumberify('<builtin>', stdlib.UInt_max, '1'), stdlib.checkedBigNumberify('<builtin>', stdlib.UInt_max, '1')];
                const v381 = v378 ? v379 : v380;
                const v382 = [stdlib.checkedBigNumberify('<builtin>', stdlib.UInt_max, '2'), stdlib.checkedBigNumberify('<builtin>', stdlib.UInt_max, '0')];
                const v383 = v377 ? v382 : v381;
                const v384 = v383[stdlib.checkedBigNumberify('./index.rsh:96:20:array', stdlib.UInt_max, '0')];
                const v385 = v383[stdlib.checkedBigNumberify('./index.rsh:96:20:array', stdlib.UInt_max, '1')];
                const v386 = stdlib.safeMul(v384, v249);
                sim_r.txns.push({
                  kind: 'from',
                  to: v248,
                  tok: undefined /* Nothing */
                  });
                const v391 = stdlib.safeMul(v385, v249);
                sim_r.txns.push({
                  kind: 'from',
                  to: v267,
                  tok: undefined /* Nothing */
                  });
                sim_r.txns.push({
                  kind: 'halt',
                  tok: undefined /* Nothing */
                  })
                sim_r.isHalt = true;
                }})();
            return sim_r;
            }),
          soloSend: true,
          timeoutAt: ['time', v325],
          tys: [ctc4, ctc0, ctc0, ctc4, ctc0, ctc0, ctc2, ctc0, ctc0, ctc0, ctc0],
          waitIfNotPresent: false
          }));
        if (txn5.didTimeout) {
          const txn6 = await (ctc.sendrecv({
            args: [v248, v249, v251, v267, v274, v283, v299, v315, v325],
            evt_cnt: 0,
            funcNum: 8,
            lct: v316,
            onlyIf: true,
            out_tys: [],
            pay: [stdlib.checkedBigNumberify('reach standard library:197:11:decimal', stdlib.UInt_max, '0'), []],
            sim_p: (async (txn6) => {
              const sim_r = { txns: [], mapRefs: [], maps: [] };
              let sim_txn_ctr = stdlib.UInt_max;
              const getSimTokCtr = () => { sim_txn_ctr = sim_txn_ctr.sub(1); return sim_txn_ctr; };
              
              
              const {data: [], secs: v343, time: v342, didSend: v119, from: v341 } = txn6;
              
              ;
              sim_r.txns.push({
                kind: 'from',
                to: v267,
                tok: undefined /* Nothing */
                });
              sim_r.txns.push({
                kind: 'halt',
                tok: undefined /* Nothing */
                })
              sim_r.isHalt = true;
              
              return sim_r;
              }),
            soloSend: false,
            timeoutAt: undefined /* mto */,
            tys: [ctc4, ctc0, ctc0, ctc4, ctc0, ctc0, ctc2, ctc0, ctc0],
            waitIfNotPresent: false
            }));
          const {data: [], secs: v343, time: v342, didSend: v119, from: v341 } = txn6;
          ;
          const v344 = stdlib.addressEq(v248, v341);
          const v345 = stdlib.addressEq(v267, v341);
          const v346 = v344 ? true : v345;
          stdlib.assert(v346, {
            at: 'reach standard library:197:11:dot',
            fs: ['at ./index.rsh:91:70:application call to "closeTo" (defined at: reach standard library:195:8:function exp)'],
            msg: 'sender correct',
            who: 'A'
            });
          ;
          stdlib.protect(ctc3, await interact.informTimeout(), {
            at: './index.rsh:50:29:application',
            fs: ['at ./index.rsh:49:9:application call to [unknown function] (defined at: ./index.rsh:49:21:function exp)', 'at reach standard library:200:8:application call to "after" (defined at: ./index.rsh:48:28:function exp)', 'at ./index.rsh:91:70:application call to "closeTo" (defined at: reach standard library:195:8:function exp)'],
            msg: 'informTimeout',
            who: 'A'
            });
          
          return;
          
          }
        else {
          const {data: [v330, v331], secs: v333, time: v332, didSend: v92, from: v329 } = txn5;
          ;
          const v334 = stdlib.addressEq(v248, v329);
          stdlib.assert(v334, {
            at: './index.rsh:91:5:dot',
            fs: [],
            msg: 'sender correct',
            who: 'A'
            });
          const v335 = stdlib.digest(ctc1, [v330, v331]);
          const v336 = stdlib.digestEq(v299, v335);
          stdlib.assert(v336, {
            at: 'reach standard library:69:17:application',
            fs: ['at ./index.rsh:92:18:application call to "checkCommitment" (defined at: reach standard library:68:8:function exp)'],
            msg: null,
            who: 'A'
            });
          let v337;
          const v338 = stdlib.eq(v315, v331);
          if (v338) {
            v337 = stdlib.checkedBigNumberify('./index.rsh:8:16:decimal', stdlib.UInt_max, '1');
            }
          else {
            const v339 = stdlib.eq(v315, v274);
            if (v339) {
              v337 = stdlib.checkedBigNumberify('./index.rsh:12:17:decimal', stdlib.UInt_max, '0');
              }
            else {
              const v340 = stdlib.eq(v331, v274);
              if (v340) {
                v337 = stdlib.checkedBigNumberify('./index.rsh:16:17:decimal', stdlib.UInt_max, '2');
                }
              else {
                v337 = stdlib.checkedBigNumberify('./index.rsh:19:16:decimal', stdlib.UInt_max, '1');
                }
              }
            }
          const cv275 = v337;
          const cv276 = v332;
          const cv283 = v283;
          
          v275 = cv275;
          v276 = cv276;
          v283 = cv283;
          
          continue;}
        
        }
      
      
      
      }
    const v377 = stdlib.eq(v275, stdlib.checkedBigNumberify('./index.rsh:97:14:decimal', stdlib.UInt_max, '2'));
    const v378 = stdlib.eq(v275, stdlib.checkedBigNumberify('./index.rsh:98:14:decimal', stdlib.UInt_max, '0'));
    const v379 = [stdlib.checkedBigNumberify('<builtin>', stdlib.UInt_max, '0'), stdlib.checkedBigNumberify('<builtin>', stdlib.UInt_max, '2')];
    const v380 = [stdlib.checkedBigNumberify('<builtin>', stdlib.UInt_max, '1'), stdlib.checkedBigNumberify('<builtin>', stdlib.UInt_max, '1')];
    const v381 = v378 ? v379 : v380;
    const v382 = [stdlib.checkedBigNumberify('<builtin>', stdlib.UInt_max, '2'), stdlib.checkedBigNumberify('<builtin>', stdlib.UInt_max, '0')];
    const v383 = v377 ? v382 : v381;
    const v384 = v383[stdlib.checkedBigNumberify('./index.rsh:96:20:array', stdlib.UInt_max, '0')];
    const v385 = v383[stdlib.checkedBigNumberify('./index.rsh:96:20:array', stdlib.UInt_max, '1')];
    const v386 = stdlib.safeMul(v384, v249);
    ;
    const v391 = stdlib.safeMul(v385, v249);
    ;
    stdlib.protect(ctc3, await interact.seeOutcome(v275, v274), {
      at: './index.rsh:104:24:application',
      fs: ['at ./index.rsh:103:7:application call to [unknown function] (defined at: ./index.rsh:103:19:function exp)'],
      msg: 'seeOutcome',
      who: 'A'
      });
    
    return;
    }
  
  
  
  };
export async function B(ctcTop, interact) {
  if (typeof(ctcTop) !== 'object' || ctcTop._initialize === undefined) {
    return Promise.reject(new Error(`The backend for B expects to receive a contract as its first argument.`));}
  if (typeof(interact) !== 'object') {
    return Promise.reject(new Error(`The backend for B expects to receive an interact object as its second argument.`));}
  const ctc = ctcTop._initialize();
  const stdlib = ctc.stdlib;
  const ctc0 = stdlib.T_UInt;
  const ctc1 = stdlib.T_Null;
  const ctc2 = stdlib.T_Digest;
  const ctc3 = stdlib.T_Tuple([ctc0, ctc0]);
  const ctc4 = stdlib.T_Address;
  
  
  const txn1 = await (ctc.recv({
    didSend: false,
    evt_cnt: 3,
    funcNum: 0,
    out_tys: [ctc0, ctc0, ctc0],
    timeoutAt: undefined /* mto */,
    waitIfNotPresent: false
    }));
  const {data: [v249, v250, v251], secs: v253, time: v252, didSend: v33, from: v248 } = txn1;
  ;
  const v262 = stdlib.safeAdd(v252, v251);
  stdlib.protect(ctc1, await interact.acceptWager(v249), {
    at: './index.rsh:62:25:application',
    fs: ['at ./index.rsh:61:9:application call to [unknown function] (defined at: ./index.rsh:61:13:function exp)'],
    msg: 'acceptWager',
    who: 'B'
    });
  const v266 = stdlib.protect(ctc0, await interact.getRandomNumber(), {
    at: './index.rsh:63:56:application',
    fs: ['at ./index.rsh:61:9:application call to [unknown function] (defined at: ./index.rsh:61:13:function exp)'],
    msg: 'getRandomNumber',
    who: 'B'
    });
  
  const txn2 = await (ctc.sendrecv({
    args: [v248, v249, v250, v251, v262, v266],
    evt_cnt: 1,
    funcNum: 1,
    lct: v252,
    onlyIf: true,
    out_tys: [ctc0],
    pay: [v249, []],
    sim_p: (async (txn2) => {
      const sim_r = { txns: [], mapRefs: [], maps: [] };
      let sim_txn_ctr = stdlib.UInt_max;
      const getSimTokCtr = () => { sim_txn_ctr = sim_txn_ctr.sub(1); return sim_txn_ctr; };
      
      
      const {data: [v268], secs: v270, time: v269, didSend: v44, from: v267 } = txn2;
      
      const v272 = stdlib.safeAdd(v249, v249);
      sim_r.txns.push({
        amt: v249,
        kind: 'to',
        tok: undefined /* Nothing */
        });
      const v273 = stdlib.safeAdd(v268, v250);
      const v274 = stdlib.safeDiv(v273, stdlib.checkedBigNumberify('./index.rsh:67:31:decimal', stdlib.UInt_max, '2'));
      const v275 = stdlib.checkedBigNumberify('./index.rsh:makeEnum', stdlib.UInt_max, '1');
      const v276 = v269;
      const v283 = v272;
      
      if (await (async () => {
        const v291 = stdlib.eq(v275, stdlib.checkedBigNumberify('./index.rsh:makeEnum', stdlib.UInt_max, '1'));
        
        return v291;})()) {
        sim_r.isHalt = false;
        }
      else {
        const v377 = stdlib.eq(v275, stdlib.checkedBigNumberify('./index.rsh:97:14:decimal', stdlib.UInt_max, '2'));
        const v378 = stdlib.eq(v275, stdlib.checkedBigNumberify('./index.rsh:98:14:decimal', stdlib.UInt_max, '0'));
        const v379 = [stdlib.checkedBigNumberify('<builtin>', stdlib.UInt_max, '0'), stdlib.checkedBigNumberify('<builtin>', stdlib.UInt_max, '2')];
        const v380 = [stdlib.checkedBigNumberify('<builtin>', stdlib.UInt_max, '1'), stdlib.checkedBigNumberify('<builtin>', stdlib.UInt_max, '1')];
        const v381 = v378 ? v379 : v380;
        const v382 = [stdlib.checkedBigNumberify('<builtin>', stdlib.UInt_max, '2'), stdlib.checkedBigNumberify('<builtin>', stdlib.UInt_max, '0')];
        const v383 = v377 ? v382 : v381;
        const v384 = v383[stdlib.checkedBigNumberify('./index.rsh:96:20:array', stdlib.UInt_max, '0')];
        const v385 = v383[stdlib.checkedBigNumberify('./index.rsh:96:20:array', stdlib.UInt_max, '1')];
        const v386 = stdlib.safeMul(v384, v249);
        sim_r.txns.push({
          kind: 'from',
          to: v248,
          tok: undefined /* Nothing */
          });
        const v391 = stdlib.safeMul(v385, v249);
        sim_r.txns.push({
          kind: 'from',
          to: v267,
          tok: undefined /* Nothing */
          });
        sim_r.txns.push({
          kind: 'halt',
          tok: undefined /* Nothing */
          })
        sim_r.isHalt = true;
        }
      return sim_r;
      }),
    soloSend: true,
    timeoutAt: ['time', v262],
    tys: [ctc4, ctc0, ctc0, ctc0, ctc0, ctc0],
    waitIfNotPresent: false
    }));
  if (txn2.didTimeout) {
    const txn3 = await (ctc.sendrecv({
      args: [v248, v249, v250, v251, v262],
      evt_cnt: 0,
      funcNum: 2,
      lct: v252,
      onlyIf: true,
      out_tys: [],
      pay: [stdlib.checkedBigNumberify('reach standard library:197:11:decimal', stdlib.UInt_max, '0'), []],
      sim_p: (async (txn3) => {
        const sim_r = { txns: [], mapRefs: [], maps: [] };
        let sim_txn_ctr = stdlib.UInt_max;
        const getSimTokCtr = () => { sim_txn_ctr = sim_txn_ctr.sub(1); return sim_txn_ctr; };
        
        
        const {data: [], secs: v404, time: v403, didSend: v209, from: v402 } = txn3;
        
        ;
        sim_r.txns.push({
          kind: 'from',
          to: v248,
          tok: undefined /* Nothing */
          });
        sim_r.txns.push({
          kind: 'halt',
          tok: undefined /* Nothing */
          })
        sim_r.isHalt = true;
        
        return sim_r;
        }),
      soloSend: false,
      timeoutAt: undefined /* mto */,
      tys: [ctc4, ctc0, ctc0, ctc0, ctc0],
      waitIfNotPresent: false
      }));
    const {data: [], secs: v404, time: v403, didSend: v209, from: v402 } = txn3;
    ;
    ;
    stdlib.protect(ctc1, await interact.informTimeout(), {
      at: './index.rsh:50:29:application',
      fs: ['at ./index.rsh:49:9:application call to [unknown function] (defined at: ./index.rsh:49:21:function exp)', 'at reach standard library:200:8:application call to "after" (defined at: ./index.rsh:48:28:function exp)', 'at ./index.rsh:65:78:application call to "closeTo" (defined at: reach standard library:195:8:function exp)'],
      msg: 'informTimeout',
      who: 'B'
      });
    
    return;
    
    }
  else {
    const {data: [v268], secs: v270, time: v269, didSend: v44, from: v267 } = txn2;
    const v272 = stdlib.safeAdd(v249, v249);
    ;
    const v273 = stdlib.safeAdd(v268, v250);
    const v274 = stdlib.safeDiv(v273, stdlib.checkedBigNumberify('./index.rsh:67:31:decimal', stdlib.UInt_max, '2'));
    let v275 = stdlib.checkedBigNumberify('./index.rsh:makeEnum', stdlib.UInt_max, '1');
    let v276 = v269;
    let v283 = v272;
    
    while (await (async () => {
      const v291 = stdlib.eq(v275, stdlib.checkedBigNumberify('./index.rsh:makeEnum', stdlib.UInt_max, '1'));
      
      return v291;})()) {
      const txn3 = await (ctc.recv({
        didSend: false,
        evt_cnt: 1,
        funcNum: 4,
        out_tys: [ctc2],
        timeoutAt: undefined /* mto */,
        waitIfNotPresent: false
        }));
      const {data: [v299], secs: v301, time: v300, didSend: v72, from: v298 } = txn3;
      ;
      const v302 = stdlib.addressEq(v248, v298);
      stdlib.assert(v302, {
        at: './index.rsh:78:5:dot',
        fs: [],
        msg: 'sender correct',
        who: 'B'
        });
      const v309 = stdlib.safeAdd(v300, v251);
      const v313 = stdlib.protect(ctc0, await interact.getGuess(), {
        at: './index.rsh:83:48:application',
        fs: ['at ./index.rsh:82:9:application call to [unknown function] (defined at: ./index.rsh:82:13:function exp)'],
        msg: 'getGuess',
        who: 'B'
        });
      
      const txn4 = await (ctc.sendrecv({
        args: [v248, v249, v251, v267, v274, v283, v299, v309, v313],
        evt_cnt: 1,
        funcNum: 5,
        lct: v300,
        onlyIf: true,
        out_tys: [ctc0],
        pay: [stdlib.checkedBigNumberify('./index.rsh:85:5:decimal', stdlib.UInt_max, '0'), []],
        sim_p: (async (txn4) => {
          const sim_r = { txns: [], mapRefs: [], maps: [] };
          let sim_txn_ctr = stdlib.UInt_max;
          const getSimTokCtr = () => { sim_txn_ctr = sim_txn_ctr.sub(1); return sim_txn_ctr; };
          
          
          const {data: [v315], secs: v317, time: v316, didSend: v82, from: v314 } = txn4;
          
          ;
          const v325 = stdlib.safeAdd(v316, v251);
          sim_r.isHalt = false;
          
          return sim_r;
          }),
        soloSend: true,
        timeoutAt: ['time', v309],
        tys: [ctc4, ctc0, ctc0, ctc4, ctc0, ctc0, ctc2, ctc0, ctc0],
        waitIfNotPresent: false
        }));
      if (txn4.didTimeout) {
        const txn5 = await (ctc.sendrecv({
          args: [v248, v249, v251, v267, v274, v283, v299, v309],
          evt_cnt: 0,
          funcNum: 6,
          lct: v300,
          onlyIf: true,
          out_tys: [],
          pay: [stdlib.checkedBigNumberify('reach standard library:197:11:decimal', stdlib.UInt_max, '0'), []],
          sim_p: (async (txn5) => {
            const sim_r = { txns: [], mapRefs: [], maps: [] };
            let sim_txn_ctr = stdlib.UInt_max;
            const getSimTokCtr = () => { sim_txn_ctr = sim_txn_ctr.sub(1); return sim_txn_ctr; };
            
            
            const {data: [], secs: v361, time: v360, didSend: v153, from: v359 } = txn5;
            
            ;
            sim_r.txns.push({
              kind: 'from',
              to: v248,
              tok: undefined /* Nothing */
              });
            sim_r.txns.push({
              kind: 'halt',
              tok: undefined /* Nothing */
              })
            sim_r.isHalt = true;
            
            return sim_r;
            }),
          soloSend: false,
          timeoutAt: undefined /* mto */,
          tys: [ctc4, ctc0, ctc0, ctc4, ctc0, ctc0, ctc2, ctc0],
          waitIfNotPresent: false
          }));
        const {data: [], secs: v361, time: v360, didSend: v153, from: v359 } = txn5;
        ;
        const v362 = stdlib.addressEq(v248, v359);
        const v363 = stdlib.addressEq(v267, v359);
        const v364 = v362 ? true : v363;
        stdlib.assert(v364, {
          at: 'reach standard library:197:11:dot',
          fs: ['at ./index.rsh:85:66:application call to "closeTo" (defined at: reach standard library:195:8:function exp)'],
          msg: 'sender correct',
          who: 'B'
          });
        ;
        stdlib.protect(ctc1, await interact.informTimeout(), {
          at: './index.rsh:50:29:application',
          fs: ['at ./index.rsh:49:9:application call to [unknown function] (defined at: ./index.rsh:49:21:function exp)', 'at reach standard library:200:8:application call to "after" (defined at: ./index.rsh:48:28:function exp)', 'at ./index.rsh:85:66:application call to "closeTo" (defined at: reach standard library:195:8:function exp)'],
          msg: 'informTimeout',
          who: 'B'
          });
        
        return;
        
        }
      else {
        const {data: [v315], secs: v317, time: v316, didSend: v82, from: v314 } = txn4;
        ;
        const v318 = stdlib.addressEq(v267, v314);
        stdlib.assert(v318, {
          at: './index.rsh:85:5:dot',
          fs: [],
          msg: 'sender correct',
          who: 'B'
          });
        const v325 = stdlib.safeAdd(v316, v251);
        const txn5 = await (ctc.recv({
          didSend: false,
          evt_cnt: 2,
          funcNum: 7,
          out_tys: [ctc0, ctc0],
          timeoutAt: ['time', v325],
          waitIfNotPresent: false
          }));
        if (txn5.didTimeout) {
          const txn6 = await (ctc.sendrecv({
            args: [v248, v249, v251, v267, v274, v283, v299, v315, v325],
            evt_cnt: 0,
            funcNum: 8,
            lct: v316,
            onlyIf: true,
            out_tys: [],
            pay: [stdlib.checkedBigNumberify('reach standard library:197:11:decimal', stdlib.UInt_max, '0'), []],
            sim_p: (async (txn6) => {
              const sim_r = { txns: [], mapRefs: [], maps: [] };
              let sim_txn_ctr = stdlib.UInt_max;
              const getSimTokCtr = () => { sim_txn_ctr = sim_txn_ctr.sub(1); return sim_txn_ctr; };
              
              
              const {data: [], secs: v343, time: v342, didSend: v119, from: v341 } = txn6;
              
              ;
              sim_r.txns.push({
                kind: 'from',
                to: v267,
                tok: undefined /* Nothing */
                });
              sim_r.txns.push({
                kind: 'halt',
                tok: undefined /* Nothing */
                })
              sim_r.isHalt = true;
              
              return sim_r;
              }),
            soloSend: false,
            timeoutAt: undefined /* mto */,
            tys: [ctc4, ctc0, ctc0, ctc4, ctc0, ctc0, ctc2, ctc0, ctc0],
            waitIfNotPresent: false
            }));
          const {data: [], secs: v343, time: v342, didSend: v119, from: v341 } = txn6;
          ;
          const v344 = stdlib.addressEq(v248, v341);
          const v345 = stdlib.addressEq(v267, v341);
          const v346 = v344 ? true : v345;
          stdlib.assert(v346, {
            at: 'reach standard library:197:11:dot',
            fs: ['at ./index.rsh:91:70:application call to "closeTo" (defined at: reach standard library:195:8:function exp)'],
            msg: 'sender correct',
            who: 'B'
            });
          ;
          stdlib.protect(ctc1, await interact.informTimeout(), {
            at: './index.rsh:50:29:application',
            fs: ['at ./index.rsh:49:9:application call to [unknown function] (defined at: ./index.rsh:49:21:function exp)', 'at reach standard library:200:8:application call to "after" (defined at: ./index.rsh:48:28:function exp)', 'at ./index.rsh:91:70:application call to "closeTo" (defined at: reach standard library:195:8:function exp)'],
            msg: 'informTimeout',
            who: 'B'
            });
          
          return;
          
          }
        else {
          const {data: [v330, v331], secs: v333, time: v332, didSend: v92, from: v329 } = txn5;
          ;
          const v334 = stdlib.addressEq(v248, v329);
          stdlib.assert(v334, {
            at: './index.rsh:91:5:dot',
            fs: [],
            msg: 'sender correct',
            who: 'B'
            });
          const v335 = stdlib.digest(ctc3, [v330, v331]);
          const v336 = stdlib.digestEq(v299, v335);
          stdlib.assert(v336, {
            at: 'reach standard library:69:17:application',
            fs: ['at ./index.rsh:92:18:application call to "checkCommitment" (defined at: reach standard library:68:8:function exp)'],
            msg: null,
            who: 'B'
            });
          let v337;
          const v338 = stdlib.eq(v315, v331);
          if (v338) {
            v337 = stdlib.checkedBigNumberify('./index.rsh:8:16:decimal', stdlib.UInt_max, '1');
            }
          else {
            const v339 = stdlib.eq(v315, v274);
            if (v339) {
              v337 = stdlib.checkedBigNumberify('./index.rsh:12:17:decimal', stdlib.UInt_max, '0');
              }
            else {
              const v340 = stdlib.eq(v331, v274);
              if (v340) {
                v337 = stdlib.checkedBigNumberify('./index.rsh:16:17:decimal', stdlib.UInt_max, '2');
                }
              else {
                v337 = stdlib.checkedBigNumberify('./index.rsh:19:16:decimal', stdlib.UInt_max, '1');
                }
              }
            }
          const cv275 = v337;
          const cv276 = v332;
          const cv283 = v283;
          
          v275 = cv275;
          v276 = cv276;
          v283 = cv283;
          
          continue;}
        
        }
      
      
      
      }
    const v377 = stdlib.eq(v275, stdlib.checkedBigNumberify('./index.rsh:97:14:decimal', stdlib.UInt_max, '2'));
    const v378 = stdlib.eq(v275, stdlib.checkedBigNumberify('./index.rsh:98:14:decimal', stdlib.UInt_max, '0'));
    const v379 = [stdlib.checkedBigNumberify('<builtin>', stdlib.UInt_max, '0'), stdlib.checkedBigNumberify('<builtin>', stdlib.UInt_max, '2')];
    const v380 = [stdlib.checkedBigNumberify('<builtin>', stdlib.UInt_max, '1'), stdlib.checkedBigNumberify('<builtin>', stdlib.UInt_max, '1')];
    const v381 = v378 ? v379 : v380;
    const v382 = [stdlib.checkedBigNumberify('<builtin>', stdlib.UInt_max, '2'), stdlib.checkedBigNumberify('<builtin>', stdlib.UInt_max, '0')];
    const v383 = v377 ? v382 : v381;
    const v384 = v383[stdlib.checkedBigNumberify('./index.rsh:96:20:array', stdlib.UInt_max, '0')];
    const v385 = v383[stdlib.checkedBigNumberify('./index.rsh:96:20:array', stdlib.UInt_max, '1')];
    const v386 = stdlib.safeMul(v384, v249);
    ;
    const v391 = stdlib.safeMul(v385, v249);
    ;
    stdlib.protect(ctc1, await interact.seeOutcome(v275, v274), {
      at: './index.rsh:104:24:application',
      fs: ['at ./index.rsh:103:7:application call to [unknown function] (defined at: ./index.rsh:103:19:function exp)'],
      msg: 'seeOutcome',
      who: 'B'
      });
    
    return;
    }
  
  
  
  };
const _ALGO = {
  ABI: {
    impure: [],
    pure: [],
    sigs: []
    },
  appApproval: `BiANAAEIWAIgBSgGUIABiAE4JgMBAAEBACI1ADEYQQTfKmRJIls1ASRbNQI2GgAXSUEAByI1BCM1BgA2GgIXNQQ2GgM2GgEXSSEGDEACCkmBBwxAAQlJJAxAAFQkEkQkNAESRDQESSISTDQCEhFEKGQpZFBJNQNXMCA1/4AEF/zbLrAyBjQDIQtbD0Q0A1cAIDEAEjT/MQASEUSxIrIBNAMlW7III7IQNP+yB7NCBABIJDQBEkQ0BEkiEkw0AhIRRChkKWRQSTUDSUlXACA1/yEJWzX+IQpbNf1JNQVJIls1/CRbNfuABIJre3Y0/BZQNPsWULAyBjQDIQtbDEQ0/zEAEkQ0A1dgIDT8FjT7FlABEkQ0/TT7EkEABiM1+kIAIDT9NP4SQQAGIjX6QgASNPs0/hJBAAchBDX6QgADIzX6NP80AyEFWzQDIQdbNANXMCA0/jT6MgY0AyVbQgKiSSEIDEAAU0ghCDQBEkQ0BEkiEkw0AhIRRChkKWRQSTUDVwAgNf+ABGG0rAywMgY0AyEKWw9ENP8xABI0A1cwIDEAEhFEsSKyATQDJVuyCCOyEDT/sgezQgL3SCEINAESRDQESSISTDQCEhFEKGQpZFBJNQNJSkpJVwAgNf8hBVs1/iEHWzX9VzAgNfwhCVs1+yVbNfpXYCA1+Uk1BRc1+IAEgaqazzT4FlCwMgY0AyEKWwxENPwxABJEMgY0/Qg19zT/NP4WUDT9FlA0/FA0+xZQNPoWUDT5UDT4FlA09xZQKEsBVwB/ZylLAVd/EWdIJDUBMgY1AkICc0khBAxAANFJgQQMQACJSCEGNAESRDQESSISTDQCEhFEKGRJNQNJSkpXACA1/yEFWzX+IQdbNf1XMCA1/CEJWzX7JVs1+kk1BTX5gAQ4sCMtNPlQsDT/MQASRDIGNP0INfg0/zT+FlA0/RZQNPxQNPsWUDT6FlA0+VA0+BZQKEsBVwB/ZylLAVd/CWdIIQg1ATIGNQJCAdwhBBJEIzQBEkQ0BEkiEkw0AhIRRChkNQOABEGxQE2wMgY0AyEMWw9EsSKyATQDIQVbsggjshA0A1cAILIHs0IBf0kjDEAAXUgjNAESRDQESSISTDQCEhFEKGRJNQMhBVs1/0k1BRc1/oAE1RUZFDT+FlCwMgY0AyEMWwxENP+IAa00A1cAIDT/NAOBMFsxADT+NAMhB1sIIQQKIzIGNP9JCEIAbUiBoI0GiAGCIjQBEkQ0BEkiEkw0AhIRREk1BUlJIls1/yRbNf6BEFs1/YAE93ETTTT/FlA0/hZQNP0WULA0/4gBSDIGNP0INfwxADT/FlA0/hZQNP0WUDT8FlAoSwFXAEBnSCM1ATIGNQJCAMs1/zX+Nf01/DX7Nfo1+TX4NP0jEkEAKDT4NPkWUDT6FlA0+1A0/BZQNP8WUChLAVcAYGdIIQY1ATIGNQJCAIyAEAAAAAAAAAABAAAAAAAAAAGAEAAAAAAAAAAAAAAAAAAAAAI0/SISTYAQAAAAAAAAAAIAAAAAAAAAADT9IQQSTTX3sSKyATT3Ils0+QuyCCOyEDT4sgezsSKyATT3JFs0+QuyCCOyEDT7sgezQgAAMRkhBhJEsSKyASKyCCOyEDIJsgkyCrIHs0IABTEZIhJEKjQBFjQCFlBnNAZBAAqABBUffHU0B1CwNABJIwgyBBJEMRYSRCNDMRkiEkRC/98iMTQSRIEDMTUSRCIxNhJEIjE3EkQiNQEiNQJC/640AElKIwg1ADgHMgoSRDgQIxJEOAgSRIk=`,
  appClear: `Bg==`,
  companionInfo: null,
  extraPages: 0,
  mapDataKeys: 0,
  mapDataSize: 0,
  stateKeys: 2,
  stateSize: 144,
  unsupported: [],
  version: 10,
  warnings: []
  };
const _ETH = {
  ABI: `[
  {
    "inputs": [
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "components": [
              {
                "internalType": "uint256",
                "name": "v249",
                "type": "uint256"
              },
              {
                "internalType": "uint256",
                "name": "v250",
                "type": "uint256"
              },
              {
                "internalType": "uint256",
                "name": "v251",
                "type": "uint256"
              }
            ],
            "internalType": "struct T1",
            "name": "msg",
            "type": "tuple"
          }
        ],
        "internalType": "struct T2",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "stateMutability": "payable",
    "type": "constructor"
  },
  {
    "inputs": [
      {
        "internalType": "uint256",
        "name": "msg",
        "type": "uint256"
      }
    ],
    "name": "ReachError",
    "type": "error"
  },
  {
    "anonymous": false,
    "inputs": [
      {
        "indexed": false,
        "internalType": "address",
        "name": "_who",
        "type": "address"
      },
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "components": [
              {
                "internalType": "uint256",
                "name": "v249",
                "type": "uint256"
              },
              {
                "internalType": "uint256",
                "name": "v250",
                "type": "uint256"
              },
              {
                "internalType": "uint256",
                "name": "v251",
                "type": "uint256"
              }
            ],
            "internalType": "struct T1",
            "name": "msg",
            "type": "tuple"
          }
        ],
        "indexed": false,
        "internalType": "struct T2",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_e0",
    "type": "event"
  },
  {
    "anonymous": false,
    "inputs": [
      {
        "indexed": false,
        "internalType": "address",
        "name": "_who",
        "type": "address"
      },
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "components": [
              {
                "internalType": "uint256",
                "name": "v268",
                "type": "uint256"
              }
            ],
            "internalType": "struct T6",
            "name": "msg",
            "type": "tuple"
          }
        ],
        "indexed": false,
        "internalType": "struct T7",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_e1",
    "type": "event"
  },
  {
    "anonymous": false,
    "inputs": [
      {
        "indexed": false,
        "internalType": "address",
        "name": "_who",
        "type": "address"
      },
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "internalType": "bool",
            "name": "msg",
            "type": "bool"
          }
        ],
        "indexed": false,
        "internalType": "struct T9",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_e2",
    "type": "event"
  },
  {
    "anonymous": false,
    "inputs": [
      {
        "indexed": false,
        "internalType": "address",
        "name": "_who",
        "type": "address"
      },
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "components": [
              {
                "internalType": "uint256",
                "name": "v299",
                "type": "uint256"
              }
            ],
            "internalType": "struct T13",
            "name": "msg",
            "type": "tuple"
          }
        ],
        "indexed": false,
        "internalType": "struct T14",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_e4",
    "type": "event"
  },
  {
    "anonymous": false,
    "inputs": [
      {
        "indexed": false,
        "internalType": "address",
        "name": "_who",
        "type": "address"
      },
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "components": [
              {
                "internalType": "uint256",
                "name": "v315",
                "type": "uint256"
              }
            ],
            "internalType": "struct T16",
            "name": "msg",
            "type": "tuple"
          }
        ],
        "indexed": false,
        "internalType": "struct T17",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_e5",
    "type": "event"
  },
  {
    "anonymous": false,
    "inputs": [
      {
        "indexed": false,
        "internalType": "address",
        "name": "_who",
        "type": "address"
      },
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "internalType": "bool",
            "name": "msg",
            "type": "bool"
          }
        ],
        "indexed": false,
        "internalType": "struct T9",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_e6",
    "type": "event"
  },
  {
    "anonymous": false,
    "inputs": [
      {
        "indexed": false,
        "internalType": "address",
        "name": "_who",
        "type": "address"
      },
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "components": [
              {
                "internalType": "uint256",
                "name": "v330",
                "type": "uint256"
              },
              {
                "internalType": "uint256",
                "name": "v331",
                "type": "uint256"
              }
            ],
            "internalType": "struct T18",
            "name": "msg",
            "type": "tuple"
          }
        ],
        "indexed": false,
        "internalType": "struct T19",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_e7",
    "type": "event"
  },
  {
    "anonymous": false,
    "inputs": [
      {
        "indexed": false,
        "internalType": "address",
        "name": "_who",
        "type": "address"
      },
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "internalType": "bool",
            "name": "msg",
            "type": "bool"
          }
        ],
        "indexed": false,
        "internalType": "struct T9",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_e8",
    "type": "event"
  },
  {
    "stateMutability": "payable",
    "type": "fallback"
  },
  {
    "inputs": [],
    "name": "_reachCreationTime",
    "outputs": [
      {
        "internalType": "uint256",
        "name": "",
        "type": "uint256"
      }
    ],
    "stateMutability": "view",
    "type": "function"
  },
  {
    "inputs": [],
    "name": "_reachCurrentState",
    "outputs": [
      {
        "internalType": "uint256",
        "name": "",
        "type": "uint256"
      },
      {
        "internalType": "bytes",
        "name": "",
        "type": "bytes"
      }
    ],
    "stateMutability": "view",
    "type": "function"
  },
  {
    "inputs": [],
    "name": "_reachCurrentTime",
    "outputs": [
      {
        "internalType": "uint256",
        "name": "",
        "type": "uint256"
      }
    ],
    "stateMutability": "view",
    "type": "function"
  },
  {
    "inputs": [
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "components": [
              {
                "internalType": "uint256",
                "name": "v268",
                "type": "uint256"
              }
            ],
            "internalType": "struct T6",
            "name": "msg",
            "type": "tuple"
          }
        ],
        "internalType": "struct T7",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_m1",
    "outputs": [],
    "stateMutability": "payable",
    "type": "function"
  },
  {
    "inputs": [
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "internalType": "bool",
            "name": "msg",
            "type": "bool"
          }
        ],
        "internalType": "struct T9",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_m2",
    "outputs": [],
    "stateMutability": "payable",
    "type": "function"
  },
  {
    "inputs": [
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "components": [
              {
                "internalType": "uint256",
                "name": "v299",
                "type": "uint256"
              }
            ],
            "internalType": "struct T13",
            "name": "msg",
            "type": "tuple"
          }
        ],
        "internalType": "struct T14",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_m4",
    "outputs": [],
    "stateMutability": "payable",
    "type": "function"
  },
  {
    "inputs": [
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "components": [
              {
                "internalType": "uint256",
                "name": "v315",
                "type": "uint256"
              }
            ],
            "internalType": "struct T16",
            "name": "msg",
            "type": "tuple"
          }
        ],
        "internalType": "struct T17",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_m5",
    "outputs": [],
    "stateMutability": "payable",
    "type": "function"
  },
  {
    "inputs": [
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "internalType": "bool",
            "name": "msg",
            "type": "bool"
          }
        ],
        "internalType": "struct T9",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_m6",
    "outputs": [],
    "stateMutability": "payable",
    "type": "function"
  },
  {
    "inputs": [
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "components": [
              {
                "internalType": "uint256",
                "name": "v330",
                "type": "uint256"
              },
              {
                "internalType": "uint256",
                "name": "v331",
                "type": "uint256"
              }
            ],
            "internalType": "struct T18",
            "name": "msg",
            "type": "tuple"
          }
        ],
        "internalType": "struct T19",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_m7",
    "outputs": [],
    "stateMutability": "payable",
    "type": "function"
  },
  {
    "inputs": [
      {
        "components": [
          {
            "internalType": "uint256",
            "name": "time",
            "type": "uint256"
          },
          {
            "internalType": "bool",
            "name": "msg",
            "type": "bool"
          }
        ],
        "internalType": "struct T9",
        "name": "_a",
        "type": "tuple"
      }
    ],
    "name": "_reach_m8",
    "outputs": [],
    "stateMutability": "payable",
    "type": "function"
  },
  {
    "stateMutability": "payable",
    "type": "receive"
  }
]`,
  Bytecode: `0x608060405260405162001d8238038062001d828339810160408190526200002691620002c9565b600080805543600355604080516020808201835292815281513381528451818501528484015180518285015293840151606082015292909101516080830152907fe875e0d974175d3036d72bf8b57156a0f70f8e5f5279acd8e22aae589e0748e69060a00160405180910390a1602082015151620000a890341460076200016a565b620000c2438360200151604001516200019560201b60201c565b81526040805160a08082018352600060208084018281528486018381526060808701858152608080890187815233808b528d8801805151885280518901518752518c015184528c518252600198899055439098558a51808801989098529451878b0152925191860191909152519084015251828401528451808303909301835260c090910190935280519192620001609260029290910190620001ec565b50505050620003c4565b81620001915760405163100960cb60e01b8152600481018290526024015b60405180910390fd5b5050565b600082620001a4838262000360565b9150811015620001e65760405162461bcd60e51b815260206004820152600c60248201526b616464206f766572666c6f7760a01b604482015260640162000188565b92915050565b828054620001fa9062000387565b90600052602060002090601f0160209004810192826200021e576000855562000269565b82601f106200023957805160ff191683800117855562000269565b8280016001018555821562000269579182015b82811115620002695782518255916020019190600101906200024c565b50620002779291506200027b565b5090565b5b808211156200027757600081556001016200027c565b604051606081016001600160401b0381118282101715620002c357634e487b7160e01b600052604160045260246000fd5b60405290565b60008183036080811215620002dd57600080fd5b604080519081016001600160401b03811182821017156200030e57634e487b7160e01b600052604160045260246000fd5b604052835181526060601f19830112156200032857600080fd5b6200033262000292565b9150602084015182526040840151602083015260608401516040830152816020820152809250505092915050565b600082198211156200038257634e487b7160e01b600052601160045260246000fd5b500190565b600181811c908216806200039c57607f821691505b60208210811415620003be57634e487b7160e01b600052602260045260246000fd5b50919050565b6119ae80620003d46000396000f3fe60806040526004361061008f5760003560e01c8063873779a111610056578063873779a11461010a578063a209ad4e1461011d578063ab53f2c614610130578063c798003714610153578063e533a29d1461016657005b80631e93b0f114610098578063422eb85c146100bc578063552d7b8e146100cf5780637eea518c146100e257806383230757146100f557005b3661009657005b005b3480156100a457600080fd5b506003545b6040519081526020015b60405180910390f35b6100966100ca36600461152d565b610179565b6100966100dd366004611557565b6103f8565b6100966100f0366004611557565b6106b3565b34801561010157600080fd5b506001546100a9565b610096610118366004611557565b610831565b61009661012b366004611557565b6109f0565b34801561013c57600080fd5b50610145610c51565b6040516100b3929190611573565b610096610161366004611557565b610cee565b610096610174366004611557565b610e85565b6101896008600054146021611021565b6101a38135158061019c57506001548235145b6022611021565b6000808055600280546101b5906115d0565b80601f01602080910402602001604051908101604052809291908181526020018280546101e1906115d0565b801561022e5780601f106102035761010080835404028352916020019161022e565b820191906000526020600020905b81548152906001019060200180831161021157829003601f168201915b50505050508060200190518101906102469190611659565b905061025e6040518060200160405280600081525090565b61027082610100015143106023611021565b604080513381528435602080830191909152850135818301529084013560608201527f443eedfa7cb93bcf21ba813a200d6756eee22aa1d3e6f8f9e753ebc0faaa84aa9060800160405180910390a16102cb3415601e611021565b81516102e3906001600160a01b03163314601f611021565b6040805161032f9161030991602080880135928801359101918252602082015260400190565b6040516020818303038152906040528051906020012060001c8360c00151146020611021565b60e082015160408401351415610348576001815261037f565b81608001518260e001511415610361576000815261037f565b60808201516040840135141561037a576002815261037f565b600181525b610387611373565b825181516001600160a01b0391821690526020808501518351820152604080860151845182015260608087015185519416930192909252608080860151845190910152835181840180519190915280514392019190915260a08501519051909101526103f281611047565b50505050565b6104086006600054146016611021565b6104228135158061041b57506001548235145b6017611021565b600080805560028054610434906115d0565b80601f0160208091040260200160405190810160405280929190818152602001828054610460906115d0565b80156104ad5780601f10610482576101008083540402835291602001916104ad565b820191906000526020600020905b81548152906001019060200180831161049057829003601f168201915b50505050508060200190518101906104c591906116e2565b90506104dd6040518060200160405280600081525090565b6104ee8260e0015143106018611021565b7f643bb8428ae07277421f7600c8b7dc078704f1cfd6d7aaedbe23c2d5754675d3338460405161051f92919061178e565b60405180910390a161053334156014611021565b606082015161054e906001600160a01b031633146015611021565b61055c438360400151611273565b81526040805161012081018252600080825260208201819052918101829052606081018290526080810182905260a0810182905260c0810182905260e0810182905261010081019190915282516001600160a01b0390811682526020808501518184015260408086015181850152606080870151909316928401929092526080808601519084015260a0808601519084015260c080860151908401528581013560e0840152835161010084015260086000554360015590516106889183910181516001600160a01b0390811682526020808401519083015260408084015190830152606080840151909116908201526080808301519082015260a0828101519082015260c0808301519082015260e0808301519082015261010091820151918101919091526101200190565b604051602081830303815290604052600290805190602001906106ac9291906113d3565b5050505050565b6106c3600160005414600d611021565b6106dd813515806106d657506001548235145b600e611021565b6000808055600280546106ef906115d0565b80601f016020809104026020016040519081016040528092919081815260200182805461071b906115d0565b80156107685780601f1061073d57610100808354040283529160200191610768565b820191906000526020600020905b81548152906001019060200180831161074b57829003601f168201915b505050505080602001905181019061078091906117b5565b90506107948160800151431015600f611021565b7f919263be6d51bec670ce110fb6a7df03fe323e3de4dade5355bccc6a4b06d95033836040516107c5929190611838565b60405180910390a16107d93415600c611021565b805160208201516040516001600160a01b039092169181156108fc0291906000818181858888f19350505050158015610816573d6000803e3d6000fd5b506000808055600181905561082d90600290611457565b5050565b6108416001600054146009611021565b61085b8135158061085457506001548235145b600a611021565b60008080556002805461086d906115d0565b80601f0160208091040260200160405190810160405280929190818152602001828054610899906115d0565b80156108e65780601f106108bb576101008083540402835291602001916108e6565b820191906000526020600020905b8154815290600101906020018083116108c957829003601f168201915b50505050508060200190518101906108fe91906117b5565b905061091181608001514310600b611021565b7f3957da95a08a7316b724c4fe20ec058158ff5f626860362a6b6aafcb999f7225338360405161094292919061178e565b60405180910390a161095b816020015134146008611021565b610963611373565b815181516001600160a01b039091169052602080830151825182015260608084015183516040908101919091528351339201919091528301516109b5916109ae919086013590611273565b60026112c6565b81516080015260208082018051600190525143908201528201516109d99080611273565b6020820151604001526109eb81611047565b505050565b610a006005600054146012611021565b610a1a81351580610a1357506001548235145b6013611021565b600080805560028054610a2c906115d0565b80601f0160208091040260200160405190810160405280929190818152602001828054610a58906115d0565b8015610aa55780601f10610a7a57610100808354040283529160200191610aa5565b820191906000526020600020905b815481529060010190602001808311610a8857829003601f168201915b5050505050806020019051810190610abd9190611875565b9050610ad56040518060200160405280600081525090565b7f117ff0fc7909f539043dcba1a015e3c49852b86bcb1c87a6cfa653f771ccbdc03384604051610b0692919061178e565b60405180910390a1610b1a34156010611021565b8151610b32906001600160a01b031633146011611021565b610b40438360400151611273565b81526040805161010081018252600080825260208201819052918101829052606081018290526080810182905260a0810182905260c0810182905260e081019190915282516001600160a01b0390811682526020808501518184015260408086015181850152606080870151909316928401929092526080808601519084015260a080860151908401528581013560c0840152835160e084015260066000554360015590516106889183910160006101008201905060018060a01b038084511683526020840151602084015260408401516040840152806060850151166060840152506080830151608083015260a083015160a083015260c083015160c083015260e083015160e083015292915050565b600060606000546002808054610c66906115d0565b80601f0160208091040260200160405190810160405280929190818152602001828054610c92906115d0565b8015610cdf5780601f10610cb457610100808354040283529160200191610cdf565b820191906000526020600020905b815481529060010190602001808311610cc257829003601f168201915b50505050509050915091509091565b610cfe600660005414601b611021565b610d1881351580610d1157506001548235145b601c611021565b600080805560028054610d2a906115d0565b80601f0160208091040260200160405190810160405280929190818152602001828054610d56906115d0565b8015610da35780601f10610d7857610100808354040283529160200191610da3565b820191906000526020600020905b815481529060010190602001808311610d8657829003601f168201915b5050505050806020019051810190610dbb91906116e2565b9050610dcf8160e00151431015601d611021565b7fcd07fe458c2837261baccc27af099290b4cb172153fe5860de83985111590dae3383604051610e00929190611838565b60405180910390a1610e1434156019611021565b8051610e48906001600160a01b03163314610e3e5760608201516001600160a01b03163314610e41565b60015b601a611021565b805160a08201516040516001600160a01b039092169181156108fc0291906000818181858888f19350505050158015610816573d6000803e3d6000fd5b610e956008600054146026611021565b610eaf81351580610ea857506001548235145b6027611021565b600080805560028054610ec1906115d0565b80601f0160208091040260200160405190810160405280929190818152602001828054610eed906115d0565b8015610f3a5780601f10610f0f57610100808354040283529160200191610f3a565b820191906000526020600020905b815481529060010190602001808311610f1d57829003601f168201915b5050505050806020019051810190610f529190611659565b9050610f678161010001514310156028611021565b7f772efef3dd9f242d63a20972cf033b16c5cb6bd8c21b19d32246dd861fb607763383604051610f98929190611838565b60405180910390a1610fac34156024611021565b8051610fe0906001600160a01b03163314610fd65760608201516001600160a01b03163314610fd9565b60015b6025611021565b80606001516001600160a01b03166108fc8260a001519081150290604051600060405180830381858888f19350505050158015610816573d6000803e3d6000fd5b8161082d5760405163100960cb60e01b8152600481018290526024015b60405180910390fd5b61104f611494565b60208201515160011415611168576110a86040518060c0016040528060006001600160a01b03168152602001600081526020016000815260200160006001600160a01b0316815260200160008152602001600081525090565b8251516001600160a01b0390811680835284516020908101518185019081528651604090810151818701908152885160609081015187168189019081528a51608090810151818b01908152878d015186015160a0808d019182526005600055436001558751998a019a909a529651958801959095529251918601919091525190951694830194909452925191810191909152905160c082015260e001604051602081830303815290604052600290805190602001906103f29291906113d3565b8051600090819052815160026020918201819052818401805160019081905290518301526040840180518290525182019290925283015151146111c157602082015151156111ba5780602001516111c7565b80516111c7565b80604001515b606082018190528251805191516020909101516001600160a01b03909216916108fc916111f391611314565b6040518115909202916000818181858888f1935050505015801561121b573d6000803e3d6000fd5b508160000151606001516001600160a01b03166108fc61124b836060015160200151856000015160200151611314565b6040518115909202916000818181858888f19350505050158015610816573d6000803e3d6000fd5b600082611280838261191f565b91508110156112c05760405162461bcd60e51b815260206004820152600c60248201526b616464206f766572666c6f7760a01b604482015260640161103e565b92915050565b6000816113035760405162461bcd60e51b815260206004820152600b60248201526a646976206279207a65726f60a81b604482015260640161103e565b61130d8284611937565b9392505050565b60008115806113385750828261132a8183611959565b92506113369083611937565b145b6112c05760405162461bcd60e51b815260206004820152600c60248201526b6d756c206f766572666c6f7760a01b604482015260640161103e565b6040805160e0810182526000918101828152606082018390526080820183905260a0820183905260c082019290925290819081526020016113ce60405180606001604052806000815260200160008152602001600081525090565b905290565b8280546113df906115d0565b90600052602060002090601f0160209004810192826114015760008555611447565b82601f1061141a57805160ff1916838001178555611447565b82800160010185558215611447579182015b8281111561144757825182559160200191906001019061142c565b50611453929150611518565b5090565b508054611463906115d0565b6000825580601f10611473575050565b601f0160209004906000526020600020908101906114919190611518565b50565b6040805160c0810190915260006080820181815260a0830191909152819081526020016114d4604051806040016040528060008152602001600081525090565b81526020016114f6604051806040016040528060008152602001600081525090565b81526020016113ce604051806040016040528060008152602001600081525090565b5b808211156114535760008155600101611519565b60006060828403121561153f57600080fd5b50919050565b60006040828403121561153f57600080fd5b60006040828403121561156957600080fd5b61130d8383611545565b82815260006020604081840152835180604085015260005b818110156115a75785810183015185820160600152820161158b565b818111156115b9576000606083870101525b50601f01601f191692909201606001949350505050565b600181811c908216806115e457607f821691505b6020821081141561153f57634e487b7160e01b600052602260045260246000fd5b604051610120810167ffffffffffffffff8111828210171561163757634e487b7160e01b600052604160045260246000fd5b60405290565b80516001600160a01b038116811461165457600080fd5b919050565b6000610120828403121561166c57600080fd5b611674611605565b61167d8361163d565b8152602083015160208201526040830151604082015261169f6060840161163d565b60608201526080830151608082015260a083015160a082015260c083015160c082015260e083015160e08201526101008084015181830152508091505092915050565b60006101008083850312156116f657600080fd5b6040519081019067ffffffffffffffff8211818310171561172757634e487b7160e01b600052604160045260246000fd5b816040526117348461163d565b815260208401516020820152604084015160408201526117566060850161163d565b60608201526080840151608082015260a084015160a082015260c084015160c082015260e084015160e0820152809250505092915050565b6001600160a01b03831681526060810161130d602083018480358252602090810135910152565b600060a082840312156117c757600080fd5b60405160a0810181811067ffffffffffffffff821117156117f857634e487b7160e01b600052604160045260246000fd5b6040526118048361163d565b8152602083015160208201526040830151604082015260608301516060820152608083015160808201528091505092915050565b6001600160a01b03831681528135602080830191909152606082019083013580151580821461186657600080fd5b80604085015250509392505050565b600060c0828403121561188757600080fd5b60405160c0810181811067ffffffffffffffff821117156118b857634e487b7160e01b600052604160045260246000fd5b6040526118c48361163d565b815260208301516020820152604083015160408201526118e66060840161163d565b60608201526080830151608082015260a083015160a08201528091505092915050565b634e487b7160e01b600052601160045260246000fd5b6000821982111561193257611932611909565b500190565b60008261195457634e487b7160e01b600052601260045260246000fd5b500490565b600081600019048311821515161561197357611973611909565b50029056fea264697066735822122056384b85592edc40d52cefd0c1290a1d00e102e2db56834c9c4f30b9d153606c64736f6c634300080c0033`,
  BytecodeLen: 7554,
  Which: `oD`,
  version: 7,
  views: {
    }
  };
export const _stateSourceMap = {
  1: {
    at: './index.rsh:59:11:after expr stmt semicolon',
    fs: [],
    msg: null,
    who: 'Module'
    },
  2: {
    at: 'reach standard library:199:11:after expr stmt semicolon',
    fs: ['at ./index.rsh:65:78:application call to "closeTo" (defined at: reach standard library:195:8:function exp)'],
    msg: null,
    who: 'Module'
    },
  4: {
    at: './index.rsh:102:11:after expr stmt semicolon',
    fs: [],
    msg: null,
    who: 'Module'
    },
  5: {
    at: './index.rsh:72:13:after expr stmt semicolon',
    fs: [],
    msg: null,
    who: 'Module'
    },
  6: {
    at: './index.rsh:79:11:after expr stmt semicolon',
    fs: [],
    msg: null,
    who: 'Module'
    },
  7: {
    at: 'reach standard library:199:11:after expr stmt semicolon',
    fs: ['at ./index.rsh:85:66:application call to "closeTo" (defined at: reach standard library:195:8:function exp)'],
    msg: null,
    who: 'Module'
    },
  8: {
    at: './index.rsh:86:11:after expr stmt semicolon',
    fs: [],
    msg: null,
    who: 'Module'
    },
  9: {
    at: 'reach standard library:199:11:after expr stmt semicolon',
    fs: ['at ./index.rsh:91:70:application call to "closeTo" (defined at: reach standard library:195:8:function exp)'],
    msg: null,
    who: 'Module'
    }
  };
export const _Connectors = {
  ALGO: _ALGO,
  ETH: _ETH
  };
export const _Participants = {
  "A": A,
  "B": B
  };
export const _APIs = {
  };
