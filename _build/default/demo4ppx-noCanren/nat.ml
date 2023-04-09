open GT
open OCanren
open OCanren.Std
type 'a0 gnat =
  | O 
  | S of 'a0 
let o () = OCanren.inj O
let s x0 = OCanren.inj (S (x0))
let rec add a b q0 =
  ((a === (o ())) &&& (b === q0)) |||
    (fresh (x) (a === (s x)) (add x (s b) q0))