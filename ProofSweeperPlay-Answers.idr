module ProofSweeperPlay
import ProofSweeperKnown
import ProofSweeperBase
import ProofSweeperLemmas

%default total
%access public export

-- Notice that 2,2 must be a mine, because...
-- Either 0,2 or 1,2 is a mine (but not both) due to 0,1 being '1'.
-- Exactly two of 0,2, 1,2, and 2,2 must be a mine, but only one of
-- 0,2 and 1,2 are a mine.

-- Let's make this into a formal proof...

mineAt2_2If0_2IsMine : MineFact (MkCoord 0 2) IsMine ->
                       MineFact (MkCoord 2 2) IsMine
mineAt2_2If0_2IsMine h0_2IsMine =
    let
      notMineAt1_2 : MineFact (MkCoord 1 2) IsNotMine =
        AllMinesAccountedFor (MkCoord 0 1) (MkCoord 1 2) NoMineAt0_1
          -- Known mines
          [MkCoord 0 2]
          -- Proof enough known mines...
          Refl
          -- Proof listed known mines are mines...
          (trueForAllListElems1 (\c : Coord => MineFact c IsMine)
            eqTestIsEqCoord
            (MkCoord 0 2) h0_2IsMine)
          -- Proof listed mines are neighbours of 0, 1....
          (trueForAllListElems1 (\c : Coord => elem c (mineNeighboursForSize (MkCoord 0 1)) = True) eqTestIsEqCoord (MkCoord 0 2) Refl)
          -- Proof 1,2 is neighbour of 0,1...
          Refl
          -- Proof 1,2 is not in list of known mines above...
          Refl
    in
      AllNonMinesAccountedFor (MkCoord 1 1) (MkCoord 2 2) NoMineAt1_1
        -- Known non mines
        [MkCoord 0 0, MkCoord 1 0, MkCoord 2 0, MkCoord 0 1,
         MkCoord 2 1, MkCoord 1 2]
        -- Proof enough non mines
        Refl
        -- Proof known non mines are not mines
        (trueForAllListElems6 (\c : Coord => MineFact c IsNotMine)
          eqTestIsEqCoord
          (MkCoord 0 0) (MkCoord 1 0) (MkCoord 2 0) (MkCoord 0 1) (MkCoord 2 1) (MkCoord 1 2)
          (KnownNotMineIsNotMine NoMineAt0_0) (KnownNotMineIsNotMine NoMineAt1_0)
          (KnownNotMineIsNotMine NoMineAt2_0) (KnownNotMineIsNotMine NoMineAt0_1)
          (KnownNotMineIsNotMine NoMineAt2_1)   notMineAt1_2)
        -- Proof known non-mines are neighbours
        (trueForAllListElems6 (\c : Coord => elem c (mineNeighboursForSize (MkCoord 1 1)) = True)
          eqTestIsEqCoord
          (MkCoord 0 0) (MkCoord 1 0) (MkCoord 2 0) (MkCoord 0 1) (MkCoord 2 1) (MkCoord 1 2)
          Refl          Refl          Refl          Refl          Refl          Refl)
        -- Proof non-mine is neighbour
        Refl
        -- Proof mine not in known non mines
        Refl

mineAt2_2If0_2IsntMine : MineFact (MkCoord 0 2) IsNotMine ->
                         MineFact (MkCoord 2 2) IsMine
mineAt2_2If0_2IsntMine prf0_2IsntMine =
  AllNonMinesAccountedFor (MkCoord 1 1) (MkCoord 2 2) NoMineAt1_1
    -- Known non mines
    [MkCoord 0 0, MkCoord 1 0, MkCoord 2 0, MkCoord 0 1, MkCoord 2 1,
     MkCoord 0 2]
    -- Proof enough non mines
    Refl
    -- Proof known non mines are not mines
    (trueForAllListElems6 (\c : Coord => MineFact c IsNotMine) eqTestIsEqCoord
      (MkCoord 0 0) (MkCoord 1 0) (MkCoord 2 0) (MkCoord 0 1) (MkCoord 2 1) (MkCoord 0 2)
      (KnownNotMineIsNotMine NoMineAt0_0) (KnownNotMineIsNotMine NoMineAt1_0)
      (KnownNotMineIsNotMine NoMineAt2_0) (KnownNotMineIsNotMine NoMineAt0_1)
      (KnownNotMineIsNotMine NoMineAt2_1) prf0_2IsntMine)
    -- Proof known non-mines are neighbours
    (trueForAllListElems6 (\c : Coord => elem c (mineNeighboursForSize (MkCoord 1 1)) = True)
      eqTestIsEqCoord
      (MkCoord 0 0) (MkCoord 1 0) (MkCoord 2 0) (MkCoord 0 1) (MkCoord 2 1)
      (MkCoord 0 2)
      Refl Refl Refl Refl Refl Refl)
    -- Proof non-mine is neighbour
    Refl
    -- Proof mine not in known non mines
    Refl

mineAt_2_2 : MineFact (MkCoord 2 2) IsMine
mineAt_2_2 = case mineOrNot (MkCoord 0 2) of
  Left prf0_2Mine => mineAt2_2If0_2IsMine prf0_2Mine
  Right prf0_2NotMine => mineAt2_2If0_2IsntMine prf0_2NotMine
