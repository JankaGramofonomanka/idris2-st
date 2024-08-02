module Control.ST.Random

import Control.ST
import Data.List
import Data.Monoid.Exponentiation
import Data.Vect

public export
Random : Type
Random = State Integer

public export
getRandom : (rnd : Var) -> ST m Integer [rnd ::: Random]
getRandom rnd =
  do
    st <- read rnd
    let st' = (1664525 * st + 1013904223) `mod` (2 ^ 32)
    write {ty = State Integer} rnd st' >>= (\_ => ST.pure st')

-- TODO I would like it to look like this
--getRandom rnd =
--  do
--    st <- read rnd
--    let st' = (1664525 * st + 1013904223) `mod` (2 ^ 32)
--    write rnd st'
--    pure st'


||| Generates a random Integer in a given range
public export
rndInt : (rnd : Var) -> Integer -> Integer -> ST m Integer [rnd ::: Random]
rndInt rnd lower upper = do
  v <- getRandom rnd
  pure $ assert_total ((v `mod` (upper - lower)) + lower)

||| Generate a random number in `Fin (S k)`
|||
||| Note that rndFin k takes values 0, 1, ..., k.
public export
rndFin : (rnd : Var) -> (k : Nat) -> ST m (Fin (S k)) [rnd ::: Random]
rndFin rnd k = do
  let v = assert_total $ !(getRandom rnd) `mod` (cast (S k))
  pure (toFin v)

  where
    toFin : Integer -> Fin (S k)
    toFin x = case integerToFin x (S k) of
      Just v  => v
      Nothing => toFin (assert_smaller x (x - cast (S k)))

||| Select a random element from a vector
public export
rndSelect' : {k : Nat} -> (rnd : Var) -> Vect (S k) a -> ST m a [rnd ::: Random]
rndSelect' {k} rnd xs = pure (Vect.index !(rndFin rnd k)  xs)

||| Select a random element from a non-empty list
rndSelect
   : (rnd     : Var)
  -> (xs      : List a)
  -> {auto ok : NonEmpty xs}
  -> ST m a [rnd ::: Random]
rndSelect rnd (x :: xs) {ok = IsNonEmpty} = pure (!(rndSelect' rnd (x::(fromList xs))))
rndSelect rnd [] {ok = IsNonEmpty} impossible
