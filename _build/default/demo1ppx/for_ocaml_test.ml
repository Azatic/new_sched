open Lib

let schedo _constraints =
  (* [%tester run_r reifier shower 1 (* принимает расписание qtrs *) searcho]
   *)
  OCanren.run
    OCanren.q
    (fun x -> Lib.searcho _constraints x)
    (fun rr -> rr#reify (reifier ()))
  |> OCanren.Stream.take ~n:1
  |> Stdlib.List.iteri (fun i ans -> Format.printf "%d: %s\n%!" i (shower ans))
;;

(* |> fun () -> assert false *)

let _ = schedo ["delete_tuesday"]
