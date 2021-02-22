{-# LANGUAGE TemplateHaskell #-}
module Types where

import           Control.Lens.TH                ( makeLenses )
import           Control.Monad.Trans.Except     ( ExceptT )
import           Control.Monad.Trans.State      ( State
                                                , StateT
                                                )

data Prop = None              -- ^ @_@
          | T                 -- ^ True
          | F                 -- ^ False
          | Atom String       -- ^ prop
          | Not Prop          -- ^ negate
          | (:/\) Prop Prop   -- ^ and
          | (:\/) Prop Prop   -- ^ or
          | (:->) Prop Prop   -- ^ imply
          | (:<->) Prop Prop  -- ^ <->

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
