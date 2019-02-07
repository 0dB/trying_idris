module Eval

-- TIL This does not mean that functions are checked for missing cases. What is the effect of this statement?

%default total

data Expr = Var String
          | Val Int
          | Add Expr Expr

-- TIL Type variable `a` is needed because:
-- `a` will be Int to start with but in the course of things it will be `Int -> Int`:
--     `pure (+) <*> eval (Var "a") : Eval (Int -> Int)`
-- and even `Int -> Int -> Int` for the type of (+):
--     `the (Eval (Int -> Int -> Int)) (pure (+)) : Eval (Int -> Int -> Int)`

data Eval : Type -> Type where
  MkEval : (List (String, Int) -> Maybe a) -> Eval a

-- I cannot interpret this REPL output for `fetch "a"`:
--     MkEval (\e => Eval.fetch, fetch' "a" e "a") : Eval Int
-- What does the comma in there mean? Why does "a" show up twice?
-- When I write fetch' so that it does does not carry x as a parameter, `fetch "a"` yields:
--     MkEval (\e => Eval.fetch, fetch' "a" e) : Eval Int

fetch : String -> Eval Int
fetch x = MkEval (\e => fetch' e) where
  fetch' : List (String, Int) -> Maybe Int
  fetch' [] = Nothing
  fetch' ((ystring, yval) :: ys) = case x == ystring of
                                     True => Just yval
                                     False => fetch' ys

Functor Eval where
  map f (MkEval g) = MkEval (\e => map f (g e))

-- TIL: Even (+) gets turned into a MkEval here:
-- `MkEval (\e => Just (\meth, meth => prim__addInt meth meth)) : Eval (Int -> Int -> Int)`
-- simplest way to find out in REPL: `the (Eval _) (pure (+))`

-- Explanations in comments below are for example `Add (Val 5) (Val 6)`

Applicative Eval where
  pure x = MkEval (\e => Just x)
  (<*>) (MkEval f) (MkEval g) = MkEval (\e => app (f e) (g e)) where
    app : Maybe (a -> b) -> Maybe a -> Maybe b
    --          ^ this is `+`     ^ and this `5` from example, or in next iteration,
    --          ^ this is `+ 5`   ^ and this `6`
    app (Just fe) (Just ge) = Just (fe ge)
    app _         _         = Nothing

-- TIL There will be no compiler warning when there are missing cases. I can ask for checking via :total eval and :missing eval
-- but can I really not get all definitions to be checked?

eval : Expr -> Eval Int
eval (Var n)   = fetch n
eval (Val v)   = pure v
eval (Add x y) = pure (+) <*> eval x <*> eval y
--               ^ this is
--                            ^ applied to this (f a)
--                                       ^ which is then applied to this (f a) b

-- valid call: `runEval [("a", 5), ("b", 12)] (Add (Val 5) (Var "a"))`

runEval : List (String, Int) -> Expr -> Maybe Int
runEval env e = case eval e of
  MkEval f => f env

-- Trying to make sense of `eval (Add (Val 5) (Var "a"))`, I shortened the output from the REPL:

{-

MkEval (\e => app Int Int
         (\e => Just (\meth => prim__addInt 5 meth))
         (\e => fetch' "a" e)
         (Just (\meth => prim__addInt 5 meth))
         (fetch' "a" e)) : Eval Int
-}
