module BNFC_Show_Doc() where
import Cl.Print

instance Show Doc where
  show = render
