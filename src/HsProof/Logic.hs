module HsProof.Logic where

import           HsProof.Types

deMorgan :: Theorem
deMorgan (Not (p :/\ q)) = Right $ Not p :\/ Not q
deMorgan (Not (p :\/ q)) = Right $ Not p :/\ Not q
deMorgan x               = Left $ Failed x

contrapostive :: Theorem
contrapostive (p :-> q) = Right $ Not q :-> Not p
contrapostive x         = Left $ Failed x

doubleNegative :: Theorem
doubleNegative (Not (Not p)) = Right p
doubleNegative x             = Left $ Failed x

eliminateDN :: Theorem
eliminateDN = Right . mapProp el
 where
  el (Not (Not p)) = el p
  el p             = p

-- not sure yet
conjunction :: Theorem'
conjunction [p, q] = Right $ p :/\ q
conjunction _      = Left $ Failed None

disjunctionL :: Theorem
disjunctionL (p :/\ _) = Right p
disjunctionL x         = Left $ Failed x

disjunctionR :: Theorem
disjunctionR (_ :/\ q) = Right q
disjunctionR x         = Left $ Failed x
