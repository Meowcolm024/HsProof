module Proof where

import           Control.Lens
import           Types

newProofObject :: Prop -> PropRef -> (ObjectId, PropRef)
newProofObject p ref = (ref ^. object & length, ref & object %~ (++ [p]))
