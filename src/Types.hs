{-# LANGUAGE TemplateHaskell #-}
module Types where

import           Control.Lens.TH                ( makeLenses )
import           Control.Monad.State            ( State )
import           Control.Monad.Trans.Except     ( ExceptT )

data Prop = None
          | Atom String
          | Not Prop
          | (:/\) Prop Prop
          | (:\/) Prop Prop
          | (:->) Prop Prop
          | (:<->) Prop Prop

instance Show Prop where
    show None       = "<X>"
    show (Atom a  ) = a
    show (Not  p  ) = "~" ++ show p
    show (a :/\  b) = "(" ++ show a ++ " /\\ " ++ show b ++ ")"
    show (a :\/  b) = "(" ++ show a ++ " \\/ " ++ show b ++ ")"
    show (p :->  q) = "(" ++ show p ++ " -> " ++ show q ++ ")"
    show (p :<-> q) = "(" ++ show p ++ " <-> " ++ show q ++ ")"

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

-- * the `Proof` type draft
type Dummy = ExceptT Prop (State PropRef)
