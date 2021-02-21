module Logic where

import           Types                          ( Prop(..), Theorem )

-- ? not sure whether it is needed
instance Eq Prop where
    None   == None   = True
    Atom a == Atom b = a == b
    _      == _      = False

deMorgan :: Theorem
deMorgan (Not (p :/\ q)) = Just $ Not p :\/ Not q
deMorgan (Not (p :\/ q)) = Just $ Not p :/\ Not q
deMorgan _               = Nothing

contrapostive :: Theorem
contrapostive (p :-> q) = Just $ Not q :-> Not p
contrapostive _         = Nothing

doubleNegative :: Theorem
doubleNegative (Not (Not p)) = Just p
doubleNegative _             = Nothing
