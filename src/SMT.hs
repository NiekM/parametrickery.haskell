{-# LANGUAGE ScopedTypeVariables #-}

module SMT (module SMT) where

import Data.SBV
import Data.SBV.Either as SBV
import Control.Monad


nat :: SInteger -> SBool
nat = (.>= 0)

fin :: SInteger -> SInteger -> SBool
fin n m = nat m .&& m .< n

-- TODO: replace with SNatural
u :: SInteger -> SInteger
u = uninterpret "u"

g :: SInteger -> SInteger -> SInteger
g = uninterpret "g"

tail1 :: Symbolic ()
tail1 = () <$ uChain 0 0 0

p0 :: SInteger -> SChar
p0 = uninterpret "p0"

extend :: Mergeable a => a -> (SInteger -> a) -> SInteger -> a
extend a f n = ite (n .== 0) a (f (n - 1))

p0B :: SInteger -> SChar
p0B = extend (literal 'B') p0

kC :: SInteger -> SChar
kC _ = literal 'C'

tail2 :: Symbolic ()
tail2 = do
  
  -- s :: SInteger <- free "s"

  -- constrain $ nat s

  -- constrain $ u s .== 1
  -- constrain $ u 0 .== s
  [s] <- uChain 0 1 1

  let
    p :: SInteger -> SChar
    p = uninterpret "p"

  gConstraint 1 s (extend (literal 'B') p) kC
  gConstraint s 0 kC p
  -- constrain \(Forall (x :: SInteger)) -> fin 1 x .=>
  --   let y = g s x in fin (1 + s) y .&& p0B y .== kC x
  -- constrain \(Forall (x :: SInteger)) -> fin s x .=>
  --   let y = g 0 x in fin (1 + 0) y .&& kC y .== p0 x

-- tail3 :: Symbolic ()
-- tail3 = do
--   [x,y] <- uChain 0 2 2
  
--   let
--     p, q, kEF :: SInteger -> SChar
--     p = uninterpret "p"
--     q = uninterpret "q"
--     kEF n = ite (n .== 0) (literal "E") (literal "F")


--   gConstraint 2 x _ _
--   gConstraint x y _ _
--   gConstraint y 0 _ _

uChain :: SInteger -> SInteger -> Int -> Symbolic [SInteger]
-- uChain s t 0 = do
--   constrain $ u s .== t
--   return []
-- uChain s t n = do
--   x :: SInteger <- symbolic ("s" <> show n)
--   constrain $ nat x
--   constrain $ u s .== x
--   (x:) <$> uChain x t (n - 1)
uChain i o n = do
  xs <- symbolics $ fmap (('s':) . show) [0 .. n - 1]
  ios u $ zip (i : xs) (xs ++ [o])
  return xs



gConstraint :: SInteger -> SInteger
  -> (SInteger -> SChar) -> (SInteger -> SChar) 
  -> Symbolic ()
gConstraint s t p q = constrain \(Forall (x :: SInteger)) -> --fin s x .=> -- Is this one necessary?
  let y = g s x in fin (1 + t) y .&& p y .== q x

-- gChain :: (SInteger -> SChar) -> (SInteger -> SChar) -> Int -> Symbolic ()
-- gChain p q 0 = do
--   constrain \(Forall (x :: SInteger)) -> fin 

-- -- foldr f [] [x_0,..,x_n-1] == [x_1,..,x_n-1]
-- mkTail :: NonEmpty SChar -> Symbolic ()
-- mkTail xs = do

--   constrain _

test :: IO SatResult
test = sat do
  -- n :: SInteger <- free "n"
  -- -- u :: SInteger -> SInteger <- free "u"
  -- constrain $ n .> 0
  -- constrain $ m .> n
  -- constrain $ u (u 0) .== 0
  tail1
  tail2



io :: EqSymbolic o => (i -> o) -> i -> o -> Symbolic ()
io f i o = constrain $ f i .== o

ios :: EqSymbolic o => (i -> o) -> [(i, o)] -> Symbolic ()
ios = mapM_ . uncurry . io


-- Constructing a foldr constraint:

shape :: EqSymbolic t => [(s, t)] -> t -> ((s, t) -> t) -> Symbolic ()
shape xs t u = ios u (zip xs (tail ts ++ [t]))
  where ts = snd <$> xs

-- pos :: [(p, q)] -> q ->  

class Dynamic a where
  dynamic :: a -> SBool

class Dynamic2 a b where
  dynamic2 :: a -> SBV b -> SBool

class (EqSymbolic s, SymVal p, Dynamic s, Dynamic2 s p) => Container s p where
  -- constrainShape :: s -> SBool
  -- conditions :: s -> p -> SBool

inOut :: (Container s p, Container t q, SymVal c)
  => (s, SBV p -> SBV c)
  -> (t, SBV q -> SBV c)
  -> (s -> t)
  -> (s -> SBV q -> SBV p)
  -> Symbolic ()
inOut (s, p) (t, q) u g = do
  constrain $ dynamic s
  constrain $ dynamic t
  constrain $ u s .== t
  constrain \(Forall x) -> dynamic2 t x .=> let y = g s x in dynamic2 s y .&& p y .== q x

-- instance Dynamic SInteger where
--   dynamic n = n .>= 0

-- instance Dynamic2 SInteger SInteger where
--   dynamic2 max n = n .>= 0 .&& n .< max

-- instance Container SInteger SInteger where
-- rev :: Symbolic ()
-- rev = do
--   u <- uninterpret "u"
--   g <- uninterpret "g"
--   inOut _ _ u g

fldr :: forall s t p q c. (EqSymbolic t, SymVal q, SymVal p, SymVal c)
  => (s -> SBool) -> (t -> SBool) -> (s -> p -> SBool) -> (t -> q -> SBool)
  -> [(s, t, SBV p -> SBV c, SBV q -> SBV c)] -> (t, SBV q -> SBV c)
  -> ((s, t) -> t) -> ((s, t) -> SBV q -> SEither p q)
  -> Symbolic ()
fldr cs ct cp cq xs o u g = 
  let os = map (\(_, t, _, q) -> (t, q)) xs ++ [o]
  in forM_ (zip xs os) \((s, t, p, q), (t', q')) -> do
    constrain $ cs s
    constrain $ ct t
    constrain $ ct t'
    constrain $ u (s, t) .== t'
    constrain \(Forall (x :: SBV q)) -> let y = g (s, t) x in SBV.either p q y .== q' x

u' :: SInteger -> SInteger -> SInteger
u' = uninterpret "shape"

g' :: SInteger -> SInteger -> SInteger -> SEither Integer Integer
g' = uninterpret "position"

-- tl3 :: Symbolic ()
-- tl3 = do
--   a <- symbolic "a"
--   b <- symbolic "b"
--   let c = uninterpret "c"
--   let d = uninterpret "d"
--   e <- symbolic "e"
--   f <- symbolic "f"
--   let g = uninterpret "g"
--   let h = uninterpret "h"
--   i <- symbolic "i"
--   j <- symbolic "j"
--   let k = uninterpret "k"
--   let l = uninterpret "l"
--   fldr nat nat fin fin [(a,b,c,d),(e,f,g,h),(i,j,k,l)] (fromList [1,2]) (uncurry u') (uncurry g')
--   -- where
--   --   q :: SInteger -> SInteger
--   --   q n = ite (n .== 0) 1 2

fromList :: Mergeable a => [a] -> (SInteger, SInteger -> a)
fromList [] = (0, undefined)
fromList [x] = (1, const x)
fromList (x:xs) = (n + 1, \m -> ite (m .== 0) x (p (m - 1)))
  where (n, p) = fromList xs

-- fldrList :: forall s t p q c . (EqSymbolic t, SymVal q, SymVal p, SymVal c) => [(s, t, SBV p -> SBV c, SBV q -> SBV c)] -> (t, SBV q -> SBV c)
--   -> ((s, t) -> t) -> ((s, t) -> SBV q -> SEither p q)
--   -> Symbolic ()
-- fldr xs o u g = 
--   let os = map (\(_, t, _, q) -> (t, q)) xs ++ [o]
--   in forM_ (zip xs os) \((s, t, p, q), (t', q')) -> do
--     constrain $ u (s, t) .== t'
--     constrain \(Forall (x :: SBV q)) -> let y = g (s, t) x in SBV.either p q y .== q' x