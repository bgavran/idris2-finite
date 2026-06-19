module Data.Finite

import Data.Vect

%default total

||| An interface for listing all values of a type with a
||| finite number of inhabitants.
public export
interface Finite a where
  constructor MkFinite
  values : List a

public export %inline
valuesOf : (0 a : Type) -> Finite a => List a
valuesOf _ = values

public export
Finite () where values = [()]

public export
Finite Void where values = []

public export
Finite Bool where values = [False,True]

public export
Finite Ordering where values = [LT,EQ,GT]

public export
Finite a => Finite (Maybe a) where values = Nothing :: map Just values

public export
Finite a => Finite b => Finite (Either a b) where
  values = map Left values ++ map Right values

public export
Finite a => Finite b => Finite (a,b) where
  values = [| MkPair values values |]

public export
{n : _} -> Finite a => Finite (Vect n a) where
  values {n = 0}   = [[]]
  values {n = S k} = [| values :: values |]

||| Denotationally equivalent to `Data.Fin.allFins`, but runs in linear,
||| instead of quadratic time. This is done by leveraging the runtime
||| optimisation of natural-number shaped datatypes as described here: 
||| https://idris2.readthedocs.io/en/latest/reference/builtins.html
||| Similar function also appears in `idris2-array` library in 
||| `Data.Array.Index.allFinsFast`
allFinsFast : (n : Nat) -> List (Fin n)
allFinsFast 0 = []
allFinsFast (S n) = go [] last
  where
    go : List (Fin k) -> Fin k -> List (Fin k)
    go xs FZ     = FZ :: xs
    go xs (FS x) = go (FS x :: xs) (assert_smaller (FS x) $ weaken x)

public export %inline
{n : _} -> Finite (Fin n) where
  values = allFinsFast n
