open Lib

(* на данный момент мы передали некоторые ограничения, но пока никак их не используем *)
open Js_of_ocaml
let schedo _constraints =
  (* [%tester run_r reifier shower 1 (* принимает расписание qtrs *) searcho]
   *)
   
  OCanren.run
    OCanren.q
    (fun x -> Lib.searcho  _constraints x)
    (fun rr -> rr#reify (reifier ()))
  |> OCanren.Stream.take ~n:1
  |> Stdlib.List.iteri (fun i ans -> Format.printf "%d: %s\n%!" i (shower ans))
;;

open Array
let _ =
  Js.export
    "myMathLib"
    (object%js
       method insSched x y = x +. y
       method abs x = abs_float x
       method generateSched ( constraints: Js.js_string Js.t Js.js_array       Js.t ) = schedo (to_list (constraints |> Js.to_array |> Array.map Js.to_string))
        
   (* let qwe :string array =    (constraints |> Js.to_array |> Array.map Js.to_string) in 
   assert false  *)
       val zero = 0.
    end)
;;
(* 
let _ =
  Js.export
    "sched"
    (object%js
       method ins_sched a b c d e = sched a b c d e
    end)
;; *)
