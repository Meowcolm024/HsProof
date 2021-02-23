{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
module HsProof.Types where

import           Control.Lens.TH                ( makeLenses )
import           Control.Monad.Trans.Except     ( ExceptT )
import           Control.Monad.Trans.State      ( State )

data Prop = None              -- ^ None
          | T                 -- ^ True
          | F                 -- ^ False
          | Atom String       -- ^ prop
          | Not Prop          -- ^ negate
          | (:/\) Prop Prop   -- ^ and
          | (:\/) Prop Prop   -- ^ or
          | (:->) Prop Prop   -- ^ imply
          | (:<->) Prop Prop  -- ^ sufficient and necessary
          deriving Eq

infix 8 :/\
infix 7 :\/
infixr 6 :->
infixr 6 :<->

instance Show Prop where
  show None       = "<X>"
  show (Atom a  ) = a
  show (Not  p  ) = "~" ++ show p
  show (a :/\  b) = "(" ++ show a ++ " /\\ " ++ show b ++ ")"
  show (a :\/  b) = "(" ++ show a ++ " \\/ " ++ show b ++ ")"
  show (p :->  q) = "(" ++ show p ++ " -> " ++ show q ++ ")"
  show (p :<-> q) = "(" ++ show p ++ " <-> " ++ show q ++ ")"

-- | apply transform function to prop
mapProp :: (Prop -> Prop) -> Prop -> Prop
mapProp _ None       = None
mapProp f T          = f T
mapProp f F          = f F
mapProp _ (Atom x  ) = Atom x
mapProp f (Not  t  ) = Not (f t)
mapProp f (p :->  q) = f p :-> f q
mapProp f (p :<-> q) = f p :<-> f q
mapProp f (p :/\  q) = f p :/\ f q
mapProp f (p :\/  q) = f p :\/ f q

-- | Reference for objects and goals during proof
data PropRef = PropRef
  {
    -- | final (sub) goals
    _goal   :: [Prop]
  ,
    -- | proof oject list
    _object :: [Prop]
  }
  deriving Show

makeLenses ''PropRef

-- | result of the proof, wither success or fail at a step 
data Result = Proved | Failed Prop deriving Show

-- * the `Proof` types
type Proof = ExceptT Result (State PropRef)
type Proof' = Proof PropRef

-- | the proof result
type ProofResult = Either Result

-- | show result
showResult :: Show a => ProofResult a -> String
showResult (Left  Proved    ) = "Q.E.D."
showResult (Left  (Failed p)) = "Proof failed with " ++ show p
showResult (Right p         ) = show p

-- id of a proof object
type ObjectId = Int

-- * theorem types
type Theorem = Prop -> Either Result Prop
type Theorem' = [Prop] -> Either Result Prop

-- * Appliable typeclass
class Appliable a b where
  app :: a -> b -> Either Result Prop

instance Appliable Prop Prop where
  -- ! x :-> y only applys to the goal
  app p@(x :-> y) q = if y == q then Right x else Left (Failed p)
  app p@(x :<-> y) q | x == q    = Right y
                     | y == q    = Right x
                     | otherwise = Left (Failed p)
  app p q = if p == q then Left Proved else Left (Failed p)

instance Appliable Theorem Prop where
  app t p = t p

instance Appliable Theorem' [Prop] where
  app t p = t p
