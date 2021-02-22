{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
module Types where

import           Control.Lens.TH                ( makeLenses )
import           Control.Monad.Trans.Except     ( ExceptT )
import           Control.Monad.Trans.State      ( State )

data Prop = None              -- ^ @_@
          | T                 -- ^ True
          | F                 -- ^ False
          | Atom String       -- ^ prop
          | Not Prop          -- ^ negate
          | (:/\) Prop Prop   -- ^ and
          | (:\/) Prop Prop   -- ^ or
          | (:->) Prop Prop   -- ^ imply
          | (:<->) Prop Prop  -- ^ <->
          deriving Eq

instance Show Prop where
  show None       = "<X>"
  show (Atom a  ) = a
  show (Not  p  ) = "~" ++ show p
  show (a :/\  b) = "(" ++ show a ++ " /\\ " ++ show b ++ ")"
  show (a :\/  b) = "(" ++ show a ++ " \\/ " ++ show b ++ ")"
  show (p :->  q) = "(" ++ show p ++ " -> " ++ show q ++ ")"
  show (p :<-> q) = "(" ++ show p ++ " <-> " ++ show q ++ ")"

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

-- * the `Proof` type draft
type Proof = ExceptT Result (State PropRef)

-- id of a proof object
type ObjectId = Int

-- * theorem types
type Theorem' = Prop -> Either Result Prop
type Theorem = [Prop] -> Either Result Prop

class Appliable a where
  app :: a -> Prop -> Either Result Prop

instance Appliable Prop where
  app p@(x :-> y) q = if y == q then Right x else Left (Failed p)
  app p           q = if p == q then Left Proved else Left (Failed p)

instance Appliable Theorem' where
  app t p = t p
