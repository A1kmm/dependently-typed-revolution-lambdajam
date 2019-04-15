data Vec : Nat -> Type -> Type where
  MkVec : (l : List a) -> Vec (length l) a

myVec : Vec 5 Nat
myVec = MkVec [1, 2, 3, 4, 5]
