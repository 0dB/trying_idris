module MyFin

data MyFin : (n : Nat) -> Type where
  MyFZ : MyFin (S k)
  MyFS : MyFin k -> MyFin (S k)

data MyVect : (a : Type) -> (n : Nat) -> Type where
  V0 : MyVect a Z
  VS : a -> MyVect a k -> MyVect a (S k)

foo : MyFin 2
foo = MyFZ

bar : MyFin 3
bar = MyFS (MyFS MyFZ)

myAdd : Maybe Int -> Maybe Int -> Maybe Int
myAdd x y = pure (+) <*> x <*> y
