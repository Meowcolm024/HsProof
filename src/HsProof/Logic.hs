module HsProof.Logic where

import           HsProof.Types

identity :: Theorem
identity (p :/\ T) = Right p
identity (p :\/ F) = Right p
identity x         = Left $ Failed x

domination :: Theorem
domination (p :/\ F) = Right F
domination (p :\/ T) = Right T
domination x         = Left $ Failed x

associative :: Theorem
associative ((p :\/ q) :\/ r        ) = Right $ p :\/ (q :\/ r)
associative (p         :\/ (q :\/ r)) = Right $ (p :\/ q) :\/ r
associative ((p :/\ q) :/\ r        ) = Right $ p :/\ (q :/\ r)
associative (p         :/\ (q :/\ r)) = Right $ (p :/\ q) :/\ r
associative x                         = Left $ Failed x

negation :: Theorem
negation x@(p :/\ (Not q)) = if p == q then Right F else Left $ Failed x
negation x@(p :\/ (Not q)) = if p == q then Right T else Left $ Failed x
negation x                 = Left $ Failed x

commutative :: Theorem
commutative (p :/\ q) = Right $ q :/\ p
commutative (p :\/ q) = Right $ q :\/ p
commutative x         = Left $ Failed x

distributive :: Theorem
distributive (p :/\ (q :\/ h)) = Right $ (p :\/ q) :/\ (p :\/ h)
distributive (p :\/ (q :/\ h)) = Right $ (p :/\ q) :\/ (p :/\ h)
distributive x                 = Left $ Failed x

deMorgan :: Theorem
deMorgan (Not (p :/\ q)  ) = Right $ Not p :\/ Not q
deMorgan (Not (p :\/ q)  ) = Right $ Not p :/\ Not q
deMorgan (Not p :/\ Not q) = Right $ Not (p :\/ q)
deMorgan (Not p :\/ Not q) = Right $ Not (p :/\ q)
deMorgan x                 = Left $ Failed x

contrapostive :: Theorem
contrapostive (p :-> q) = Right $ Not q :-> Not p
contrapostive x         = Left $ Failed x

doubleNegative :: Theorem
doubleNegative (Not (Not p)) = Right p
doubleNegative x             = Left $ Failed x

-- ? not sure yet
conjunction :: Theorem'
conjunction [p, q] = Right $ p :/\ q
conjunction _      = Left $ Failed None

simplificationL :: Theorem
simplificationL (p :/\ _) = Right p
simplificationL x         = Left $ Failed x

simplificationR :: Theorem
simplificationR (_ :/\ q) = Right q
simplificationR x         = Left $ Failed x

-- ! not quite right
addition :: Theorem'
addition [p, q] = Right $ p :\/ q
addition _      = Left $ Failed None

disjunction :: Theorem'
disjunction [p :\/ q, r@(Not _)] | r == p    = Right q
                                 | r == q    = Right p
                                 | otherwise = Left $ Failed r
disjunction _ = Left $ Failed None

-- simplify expr
simpl :: Theorem
simpl = Right . simpl'
 where
  simpl' :: Prop -> Prop
  simpl' (Not (Not p :/\ Not q)) = simpl' p :\/ simpl' q
  simpl' (Not (Not p :\/ Not q)) = simpl' p :/\ simpl' q
  simpl' (Not (Not p          )) = simpl' p
  simpl' (p :->  q             ) = simpl' p :-> simpl' q
  simpl' (p :<-> q             ) = simpl' p :<-> simpl' q
  simpl' p                       = p
