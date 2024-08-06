{-# OPTIONS --rewriting #-}
open import Calf.Data.Bool
open import Examples.Sorting.Sequential.Comparable
open import Calf hiding (A)
open import Calf.Data.Maybe

module Brodal-Okasaki (M : Comparable) where
  open Comparable M

  open import PriorityQueue M
  open import SkewBinomialHeap M using (skewBinomialHeap)

  

