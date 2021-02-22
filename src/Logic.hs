module Logic where

import           Types

-- ? not sure whether it is needed
instance Eq Prop where
    None   == None   = True
    Atom a == Atom b = a == b
    _      == _      = False

deMorgan :: Theorem'
deMorgan (Not (p :/\ q)) = Right $ Not p :\/ Not q
deMorgan (Not (p :\/ q)) = Right $ Not p :/\ Not q
deMorgan x               = Left $ Failed x

contrapostive :: Theorem'
contrapostive (p :-> q) = Right $ Not q :-> Not p
contrapostive x         = Left $ Failed x

doubleNegative :: Theorem'
doubleNegative (Not (Not p)) = Right p
doubleNegative x             = Left $ Failed x
