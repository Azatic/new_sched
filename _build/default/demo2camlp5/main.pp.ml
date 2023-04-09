open OCanren
open Tester
open Lib
open Lam

let rec substo l x a l' =
  conde
    [OCanren.Fresh.one
       (fun y ->
          delay (fun () -> conj (conj (l === v y) (y === x)) (l' === a)));
     OCanren.Fresh.three
       (fun m n m' ->
          OCanren.Fresh.one
            (fun n' ->
               delay
                 (fun () ->
                    conj
                      (conj (conj (l === app m n) (l' === app m' n'))
                         (substo m x a m'))
                      (substo n x a n'))));
     OCanren.Fresh.two
       (fun v b ->
          delay
            (fun () ->
               conj (l === abs v b)
                 (conde
                    [(x === v) &&& (l' === l);
                     OCanren.Fresh.one
                       (fun b' ->
                          delay
                            (fun () ->
                               conj (l' === abs v b') (substo b x a b')))])))]

let rec evalo m n =
  conde
    [OCanren.Fresh.one
       (fun x -> delay (fun () -> conj (m === v x) (n === m)));
     OCanren.Fresh.two
       (fun x l -> delay (fun () -> conj (m === abs x l) (n === m)));
     OCanren.Fresh.three
       (fun f a f' ->
          OCanren.Fresh.one
            (fun a' ->
               delay
                 (fun () ->
                    conj
                      (conj (conj (m === app f a) (evalo f f')) (evalo a a'))
                      (conde
                         [OCanren.Fresh.three
                            (fun x l l' ->
                               delay
                                 (fun () ->
                                    conj
                                      (conj (f' === abs x l)
                                         (substo l x a' l'))
                                      (evalo l' n)));
                          OCanren.Fresh.two
                            (fun p q ->
                               delay
                                 (fun () ->
                                    conj (f' === app p q) (n === app f' a')));
                          OCanren.Fresh.one
                            (fun x ->
                               delay
                                 (fun () ->
                                    conj (f' === v x)
                                      (n === app f' a')))]))))]

let a_la_quine q r s =
  ?&[evalo (app q r) s; evalo (app r s) q; evalo (app s q) r]

open Tester

let runL eta = run_r Lam.reify (GT.show Lam.logic) eta
let run_exn eta = run_r Lam.prj_exn eta

let _ =
  run_exn (GT.show Lam.ground) 1 q qh
    ("fun q -> substo (v varX) varX (v varY) q",
     (fun q -> substo (v varX) varX (v varY) q));
  run_exn (GT.show Lam.ground) 1 q qh
    ("fun q -> evalo (abs varX (v varX)) q",
     (fun q -> evalo (abs varX (v varX)) q));
  run_exn (GT.show Lam.ground) 2 q qh
    ("fun q -> evalo (abs varX (v varX)) q",
     (fun q -> evalo (abs varX (v varX)) q));
  run_exn (GT.show Lam.ground) 1 q qh
    ("fun q -> evalo (app (abs varX (v varX)) (v varY)) q",
     (fun q -> evalo (app (abs varX (v varX)) (v varY)) q));
  run_exn (GT.show Lam.ground) 1 q qh
    ("fun q -> evalo (app (abs varX (v varX)) q) (v varY)",
     (fun q -> evalo (app (abs varX (v varX)) q) (v varY)));
  run_exn (GT.show Lam.ground) 1 q qh
    ("fun q -> evalo (app (abs varX q) (v varY)) (v varY)",
     (fun q -> evalo (app (abs varX q) (v varY)) (v varY)));
  run_exn (GT.show Lam.ground) 1 q qh
    ("fun q -> evalo (app (v varX) (v varX)) q",
     (fun q -> evalo (app (v varX) (v varX)) q));
  run_exn (GT.show Lam.ground) 1 q qh
    ("fun q -> evalo (v varX) q", (fun q -> evalo (v varX) q))

let _withFree =
  runL 1 q qh
    ("fun q -> evalo (app q (v varX)) (v varX)",
     (fun q -> evalo (app q (v varX)) (v varX)));
  runL 1 qr qrh
    ("fun q r -> evalo (app r q) (v varX)",
     (fun q r -> evalo (app r q) (v varX)));
  runL 2 qrs qrsh
    ("fun q r s -> a_la_quine q r s", (fun q r s -> a_la_quine q r s))
