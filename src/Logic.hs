module Logic where

data Prop = Atom String
          | Prop
          | Not Prop
          | (:&&) Prop Prop
          | (:||) Prop Prop
          | (:->) Prop Prop
          | (:<->) Prop Prop
          deriving Show
