'reach 0.1';

const [ isOutcome, A_Win, DRAW, B_Win] = makeEnum(3);

const winner = (x, guessA, guessB) => {
    if(guessB==guessA)
    {
        return 1;
    }
    else if (guessB == x) 
    {
         return 0;
    }
    else if(guessA == x)
    {
         return 2;
    }
    else {
        return 1;
    }
  };
const Player = {
    ...hasRandom,
    getRandomNumber:Fun([], UInt),
    getGuess: Fun([], UInt),
    seeOutcome: Fun([UInt,UInt], Null),
    informTimeout: Fun([], Null),
  };
  
export const main = Reach.App(() => {
  const A = Participant('A', {
  // Specify Alice's interact interface here
    ...Player,
    wager: UInt,
    deadline: UInt, 
  });
  const B   = Participant('B', {
  // Specify Bob's interact interface here
    ...Player,
    acceptWager: Fun([UInt], Null),
  });

  /* const B = API({ B: Fun([UInt], Bool) 
  }); */

  init();
  // The first one to publish deploys the contract
  const informTimeout = () => {
    each([A, B], () => {
      interact.informTimeout();
    });
  };
  A.only(() => {
    const wager = declassify(interact.wager);
    const randomA = declassify(interact.getRandomNumber());
    const deadline = declassify(interact.deadline);
  });
  A.publish(wager,randomA,deadline).pay(wager);;
  commit();
  // The second one to publish always attaches
  B.only(() => {
    interact.acceptWager(wager);
    const randomB = declassify(interact.getRandomNumber());
  });
  B.publish(randomB).pay(wager).timeout(relativeTime(deadline), () => closeTo(A, informTimeout));

  const x = (randomB+randomA)/2;
  var outcome = DRAW;
  invariant( balance() == 2 * wager && isOutcome(outcome) );

  while ( outcome == DRAW ) {
    commit();
  A.only(() => {
    const _guessA = interact.getGuess();
    const [_commitA, _saltA] = makeCommitment(interact, _guessA);
    const commitA = declassify(_commitA);
  });
  A.publish(commitA);
  commit();

  unknowable(B, A(_guessA, _saltA));
  B.only(() => {
    const guessB = declassify(interact.getGuess());
  });
  B.publish(guessB).timeout(relativeTime(deadline), () => closeTo(A, informTimeout));
  commit();
  A.only(() => {
    const pA = declassify(_saltA);
    const guessA = declassify(_guessA);
  });
  A.publish(pA, guessA).timeout(relativeTime(deadline), () => closeTo(B, informTimeout));;
  checkCommitment(commitA, pA, guessA);
  outcome = winner(x, guessA, guessB);
  continue;
}
  const            [forA, forB] =
  outcome == 2 ? [       2,      0] :
  outcome == 0 ? [       0,      2] :
  [       1,      1];
  transfer(forA * wager).to(A);
  transfer(forB   * wager).to(B);
  commit();
  each([A, B], () => {
    interact.seeOutcome(outcome,x);
  });
});
