open OCanren
open OCanren.Std

let rec appendo a b ab =
  conde
    [ a === nil () &&& (b === ab)
    ; fresh (h t ab') (a === h % t) (h % ab' === ab) (appendo t b ab')
    ]
;;

let rec membero x l = conde [ List.caro l x; fresh d (List.cdro l d) (membero x d) ]

(* let rec evalo m n =
  conde
    [ fresh x (m === v x) (n === m)
    ; fresh (x l) (m === abs x l) (n === m)
    ; fresh
        (f a f' a')
        (m === app f a)
        (evalo f f')
        (evalo a a')
        (conde
           [ fresh (x l l') (f' === abs x l) (substo l x a' l') (evalo l' n)
           ; fresh (p q) (f' === app p q) (n === app f' a')
           ; fresh x (f' === v x) (n === app f' a')
           ])
    ]
;; *)
(* 
let a_la_quine q r s = ?&[ evalo (app q r) s; evalo (app r s) q; evalo (app s q) r ]

open Tester

let runL n = run_r Lam.reify (GT.show Lam.logic) n
(* let run_exn eta = run_r Lam.prj_exn eta *)

let run_exn eta =
  run_r (Std.List.prj_exn OCanren.prj_exn) (GT.show Std.List.ground (GT.show GT.int)) eta
;;

let _ = run_exn (-1) qr qrh (REPR (fun q r -> appendo q r (list ( !! ) [ 1; 2; 3; 4 ])))
let relo s = s === Std.List.cons __ __
let x = GT.show Std.List.logic (GT.show GT.int) *)

(* module Para = struct
  [%%distrib
  type nonrec 'a t =
    | Lecture of 'a
    | Practice of 'a
  [@@deriving gt ~plugins:{ gmap; show }] *)
(* 
  type nonrec 'a ground = 'a t]
end *)

(* let _withFree =
  [%tester
    run_r
      (Para.reify OCanren.reify)
      (GT.show Para.logic (GT.show OCanren.logic @@ GT.show GT.string))
      3
      (fun q -> conde [ q === Para.lecture __; q === Para.practice __ ])]
;; *)

let insert_first_lesson q =
  conde [ fresh (s w e r) (q === Std.list Fun.id [ s; w; e; r ]) (s === !!"werty") ]
;;

let ins_first_lesson q lesson =
  conde [ fresh (s w e r) (q === Std.list Fun.id [ s; w; e; r ]) (s === lesson) ]
;;

let ins_second_lesson q lesson =
  conde [ fresh (s w e r) (q === Std.list Fun.id [ s; w; e; r ]) (w === lesson) ]
;;

let ins_monday_1 q lesson =
  conde
    [ fresh
        (a1 a2 a3 a4 a5 b1 b2 b3 b4)
        (q === Std.list Fun.id [ a1; a2; a3; a4; a5 ])
        (a1 === Std.list Fun.id [ b1; b2; b3; b4 ])
        (b1 === lesson)
    ]
;;

let ins_monday_2 q lesson =
  conde
    [ fresh
        (a1 a2 a3 a4 a5 b1 b2 b3 b4)
        (q === Std.list Fun.id [ a1; a2; a3; a4; a5 ])
        (a1 === Std.list Fun.id [ b1; b2; b3; b4 ])
        (b2 === lesson)
    ]
;;

let ins_monday_3 q lesson =
  conde
    [ fresh
        (a1 a2 a3 a4 a5 b1 b2 b3 b4)
        (q === Std.list Fun.id [ a1; a2; a3; a4; a5 ])
        (a1 === Std.list Fun.id [ b1; b2; b3; b4 ])
        (b3 === lesson)
    ]
;;

let ins_monday_4 q lesson =
  conde
    [ fresh
        (a1 a2 a3 a4 a5 b1 b2 b3 b4)
        (q === Std.list Fun.id [ a1; a2; a3; a4; a5 ])
        (a1 === Std.list Fun.id [ b1; b2; b3; b4 ])
        (b4 === lesson)
    ]
;;

let ins_tuesday_1 q lesson =
  conde
    [ fresh
        (a1 a2 a3 a4 a5 b1 b2 b3 b4)
        (q === Std.list Fun.id [ a1; a2; a3; a4; a5 ])
        (a2 === Std.list Fun.id [ b1; b2; b3; b4 ])
        (b1 === lesson)
    ]
;;

let ins_tuesday_2 q lesson =
  conde
    [ fresh
        (a1 a2 a3 a4 a5 b1 b2 b3 b4)
        (q === Std.list Fun.id [ a1; a2; a3; a4; a5 ])
        (a2 === Std.list Fun.id [ b1; b2; b3; b4 ])
        (b2 === lesson)
    ]
;;

let ins_tuesday_3 q lesson =
  conde
    [ fresh
        (a1 a2 a3 a4 a5 b1 b2 b3 b4)
        (q === Std.list Fun.id [ a1; a2; a3; a4; a5 ])
        (a2 === Std.list Fun.id [ b1; b2; b3; b4 ])
        (b3 === lesson)
    ]
;;

let ins_tuesday_4 q lesson =
  conde
    [ fresh
        (a1 a2 a3 a4 a5 b1 b2 b3 b4)
        (q === Std.list Fun.id [ a1; a2; a3; a4; a5 ])
        (a2 === Std.list Fun.id [ b1; b2; b3; b4 ])
        (b4 === lesson)
    ]
;;

let insert_lesson q lesson =
  conde
    [ ins_monday_1 q lesson
    ; ins_monday_2 q lesson
    ; ins_monday_3 q lesson
    ; ins_monday_4 q lesson
    ; ins_tuesday_1 q lesson
    ; ins_tuesday_2 q lesson
    ; ins_tuesday_3 q lesson
    ; ins_tuesday_4 q lesson
    ]
;;

let init_sched_one_day s =
  conde [ fresh (q w e r) (s === Std.list Fun.id [ q; w; e; r ]) ]
;;

let init_sched_a_week q =
  let ( ** ) = ( % ) in
  conde
    [ fresh
        (w e r t y)
        (init_sched_one_day w)
        (init_sched_one_day e)
        (init_sched_one_day r)
        (init_sched_one_day t)
        (init_sched_one_day y)
        (q === w ** e ** r ** t ** !<y)
    ]
;;

let ins_sched1 subj group_sched teacher_sched class_sched =
  conde
    [ fresh
        (a2 a3 a4 b2 b3 b4 c2 c3 c4)
        (group_sched === Std.list Fun.id [ subj; a2; a3; a4 ])
        (teacher_sched === Std.list Fun.id [ subj; b2; b3; b4 ])
        (class_sched === Std.list Fun.id [ subj; c2; c3; c4 ])
    ]
;;

let ins_sched2 subj group_sched teacher_sched class_sched =
  conde
    [ fresh
        (a2 a3 a4 b2 b3 b4 c2 c3 c4)
        (group_sched === Std.list Fun.id [ a2; subj; a3; a4 ])
        (teacher_sched === Std.list Fun.id [ b2; subj; b3; b4 ])
        (class_sched === Std.list Fun.id [ c2; subj; c3; c4 ])
    ]
;;

let ins_sched3 subj group_sched teacher_sched class_sched =
  conde
    [ fresh
        (a2 a3 a4 b2 b3 b4 c2 c3 c4)
        (group_sched === Std.list Fun.id [ a2; a3; subj; a4 ])
        (teacher_sched === Std.list Fun.id [ b2; b3; subj; b4 ])
        (class_sched === Std.list Fun.id [ c2; c3; subj; c4 ])
    ]
;;

let ins_sched4 subj group_sched teacher_sched class_sched =
  conde
    [ fresh
        (a2 a3 a4 b2 b3 b4 c2 c3 c4)
        (group_sched === Std.list Fun.id [ a2; a3; a4; subj ])
        (teacher_sched === Std.list Fun.id [ b2; b3; b4; subj ])
        (class_sched === Std.list Fun.id [ c2; c3; c4; subj ])
    ]
;;

(* let ins_sched_mon subj group_sched teacher_sched class_sched =
  conde 
  [ fresh
  
  ] *)

let insert_all_sched subj group_sched teacher_sched class_sched =
  fresh
    (a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 c1 c2 c3 c4 c5)
    (group_sched === Std.list Fun.id [ a1; a2; a3; a4; a5 ])
    (teacher_sched === Std.list Fun.id [ b1; b2; b3; b4; b5 ])
    (class_sched === Std.list Fun.id [ c1; c2; c3; c4; c5 ])
    (conde
       [ ins_sched1 subj a1 b1 c1
       ; ins_sched2 subj a1 b1 c1
       ; ins_sched3 subj a1 b1 c1
       ; ins_sched4 subj a1 b1 c1
       ; ins_sched1 subj a2 b2 c2
       ; ins_sched2 subj a2 b2 c2
       ; ins_sched3 subj a2 b2 c2
       ; ins_sched4 subj a2 b2 c2
       ; ins_sched1 subj a3 b3 c3
       ; ins_sched2 subj a3 b3 c3
       ; ins_sched3 subj a3 b3 c3
       ; ins_sched4 subj a3 b3 c3
       ; ins_sched1 subj a4 b4 c4
       ; ins_sched2 subj a4 b4 c4
       ; ins_sched3 subj a4 b4 c4
       ; ins_sched4 subj a4 b4 c4
       ])
;;

let rec insert_sched_to_one_group
  lessons
  all_teacher_sched
  sched_all_class
  group_sched
  class_subj
  =
  conde
    [ lessons === List.nil ()
    ; fresh
        (teacher_sched
           lesson
           tail_teacher
           tail_lessons
           sched_class
           ost
           class_first
           class_ost)
        (all_teacher_sched === List.cons teacher_sched tail_teacher)
        (lessons === List.cons lesson tail_lessons)
        (sched_all_class === List.cons sched_class ost)
        (class_subj === List.cons class_first class_ost)
        (membero lesson class_first)
        (insert_all_sched lesson group_sched teacher_sched sched_class)
        (insert_sched_to_one_group
           tail_lessons
           tail_teacher
           sched_all_class
           group_sched
           class_subj)
    ; fresh
        (sched_first_class ost subj_first subj_ost)
        (sched_all_class === List.cons sched_first_class ost)
        (class_subj === List.cons subj_first subj_ost)
        (insert_sched_to_one_group lessons all_teacher_sched ost group_sched subj_ost)
    ]
;;

(* let rec insert_sched all_teacher_sched sched_class group_sched all_lessons =
  conde
    [ all_lessons === List.nil ()
    ; fresh
        (teacher_sched lesson tail_teacher tail_lessons)
        (all_teacher_sched === List.cons teacher_sched tail_teacher)
        (all_lessons === List.cons lesson tail_lessons)
        (insert_lesson teacher_sched lesson)
        (insert_lesson group_sched lesson)
        (insert_lesson sched_class lesson)
        (insert_sched tail_teacher sched_class group_sched tail_lessons)
    ]
;; *)

(* (define (sched studyplanallgroup schedallgroup allteachersched schedclass classessubj allnamegroup allteachername allclassnumber) ;составляет расписание на все группы, но только практики
  (conde
   [(== studyplanallgroup '()) succeed]
   [(fresh (a1 a2 a3 namegroup schedone c4 c5) (caro studyplanallgroup a1) (caro schedallgroup schedone) (caro allnamegroup namegroup) (caro allteachersched a3) (caro allteachername c5) 
           (timetableonegroup a1 schedone a3 schedclass classessubj namegroup c5 allclassnumber))
    (fresh (a4 a5 a6 b1 b2 b3) (cdro studyplanallgroup a4) (cdro schedallgroup a5) (cdro allteachersched a6) (cdro allnamegroup b1) (cdro allteachername b2)
           (sched a4 a5 a6 schedclass classessubj b1 b2 allclassnumber))
           ]
   )) *)
let rec sched studyplanallgroup schedallgroup allteachersched schedclass classessubj =
  conde
    [ studyplanallgroup === List.nil ()
    ; schedallgroup === List.nil ()
    ; fresh
        (studyplanonegroup studyplanost schedonegroup schedost oneteacher ostteacher)
        (studyplanallgroup === List.cons studyplanonegroup studyplanost)
        (schedallgroup === List.cons schedonegroup schedost)
        (allteachersched === List.cons oneteacher ostteacher)
        (insert_sched_to_one_group
           studyplanonegroup
           oneteacher
           schedclass
           schedonegroup
           classessubj)
        (sched studyplanost schedost ostteacher schedclass classessubj)
    ]
;;

(* let delete_monday = *)

(* let _withFree =
  [%tester
    run_r
      (Std.List.reify (Std.List.reify OCanren.reify))
      (GT.show
         Std.List.logic
         (GT.show Std.List.logic (GT.show OCanren.logic @@ GT.show GT.string)))
      1
      (fun q r s t ->
        init_sched_a_week q
        &&& init_sched_a_week t
        &&& init_sched_a_week r
        &&& init_sched_a_week s
        &&& insert_sched_to_one_group
              (Std.list Fun.id [ !!"matan1"; !!"matan2"; !!"geom1"; !!"alg1" ])
              (Std.list Fun.id [ q; q; q; q ])
              (Std.list Fun.id [ s ])
              r
              (Std.list
                 Fun.id
                 [ Std.list
                     Fun.id
                     [ !!"matan1"
                     ; !!"geom1"
                     ; !!"eng1"
                     ; !!"matan3"
                     ; !!"matan4"
                     ; !!"geom2"
                     ; !!"alg2"
                     ; !!"matan2"
                     ; !!"matan6"
                     ; !!"geom2"
                     ; !!"alg1"
                     ]
                 ]))]
;; *)

(* let _withFree =
  [%tester
    run_r
      (Std.List.reify (Std.List.reify OCanren.reify))
      (GT.show
         Std.List.logic
         (GT.show Std.List.logic (GT.show OCanren.logic @@ GT.show GT.string)))
      10
      (fun q r s t ->
        init_sched_a_week q
        &&& init_sched_a_week t
        &&& init_sched_a_week r
        &&& init_sched_a_week s
        &&& sched
              (Std.list
                 Fun.id
                 [ Std.list Fun.id [ !!"matan1"; !!"matan2"; !!"geom1"; !!"alg1" ] ])
              (Std.list Fun.id [ q ])
              (Std.list Fun.id [ Std.list Fun.id [ t; t; t; t ] ])
              (Std.list Fun.id [ s ])
              (Std.list
                 Fun.id
                 [ Std.list
                     Fun.id
                     [ !!"matan1"
                     ; !!"geom1"
                     ; !!"eng1"
                     ; !!"matan3"
                     ; !!"matan4"
                     ; !!"geom2"
                     ; !!"alg2"
                     ; !!"matan2"
                     ; !!"matan6"
                     ; !!"geom2"
                     ; !!"alg1"
                     ]
                 ]))]
;; *)

(* let rec sched studyplanallgroup schedallgroup allteachersched schedclass classessubj *)
(* let _withFree =
  [%tester
    run_r
      (Std.List.reify (Std.List.reify OCanren.reify))
      (GT.show
         Std.List.logic
         (GT.show Std.List.logic (GT.show OCanren.logic @@ GT.show GT.string)))
      10
      (fun q r s ->
        init_sched_a_week q
        &&& init_sched_a_week r
        &&& init_sched_a_week s
        &&& insert_sched
              (Std.list Fun.id [ q; q; q ])
              r
              s
              (Std.list Fun.id [ !!"matan1"; !!"geom1"; !!"eng1" ]))]
;; *)

(* let _withFree =
  [%tester
    run_r
      (Std.List.reify OCanren.reify)
      (GT.show Std.List.logic (GT.show OCanren.logic @@ GT.show GT.string))
      1
      (fun q r s -> membero !!"matan" (Std.list Fun.id [ !!"matan"; !!"geom"; !!"eng" ]))
    &&& appendo q r s]
;; *)
(* let _withFree =
  [%tester
    run_r
      (Std.List.reify (Std.List.reify OCanren.reify))
      (GT.show
         Std.List.logic
         (GT.show Std.List.logic (GT.show OCanren.logic @@ GT.show GT.string)))
      1
      (fun q r s ->
        membero !!"matan" (Std.list Fun.id [ !!"atan"; !!"geom"; !!"eng" ])
        &&& appendo q r s)]
;; *)
(* let _withFree =
  [%tester
    run_r
      (Std.List.reify (Std.List.reify OCanren.reify))
      (GT.show
         Std.List.logic
         (GT.show Std.List.logic (GT.show OCanren.logic @@ GT.show GT.string)))
      10
      (fun q r s t ->
        init_sched_a_week q
        &&& Sched_core.init_sched_a_week q
        &&& init_sched_a_week t
        &&& init_sched_a_week s
        &&& insert_sched_to_one_group
              (Std.list Fun.id [ !!"matan"; !!"geom"; !!"eng" ])
              (Std.list Fun.id [ q; q; q ])
              (Std.list Fun.id [ r ])
              s
              (Std.list Fun.id [ !!"matan"; !!"geom"; !!"eng" ]))]
;; *)
(* let rec insert_sched_to_one_group lessons all_teacher_sched sched_all_class group_sched =
  conde
    [ lessons === List.nil (); fresh (teacher_sched lesson tail_teacher tail_lessons sched_class ost) 
    (all_teacher_sched === List.cons teacher_sched tail_teacher)
    (lessons === List.cons lesson tail_lessons)
    (sched_all_class === List.cons sched_class ost)
    (membero lesson sched_class)
    (insert_all_sched lesson group_sched teacher_sched sched_class)
    (insert_sched_to_one_group tail_lessons tail_teacher sched_all_class group_sched);
    
    
     ]
;; *)
(* let _withFree = runL 1 q qh (REPR (fun q -> evalo (app q (v varX)) (v varX))) *)

(* let _withFree =
  run_r
    (Std.List.reify (Std.List.reify OCanren.reify))
    (GT.show
       Std.List.logic
       (GT.show Std.List.logic (GT.show OCanren.logic @@ GT.show GT.string)))
    10
    q

let rec sched studyplanallgroup schedallgroup allteachersched schedclass classessubj  ;; *)
type week_day =
| Monday
| Tuesday
| Wednesday
| Thursday
| Friday

type user_constraints = 
| Group_not_learning of {number_lesson:int; day: week_day}

[@@@ocaml.warnerror "-27"]

(* let employ_constraint user_const q =
  Stdlib.List.fold_left (fun acc _ -> acc) success user_const
;; *)
let delete_monday q =
  conde
    [ fresh
        (a1 a2 a3 a4 a5 b1 b2 b3 b4)
        (q === Std.list Fun.id [ a1; a2; a3; a4; a5 ])
        (a1 === Std.list Fun.id [ !!"window"; !!"window"; !!"window"; !!"window" ])
    ]
;;
let delete_tuesday q =
  conde
    [ fresh
        (a1 a2 a3 a4 a5 b1 b2 b3 b4)
        (q === Std.list Fun.id [ a1; a2; a3; a4; a5 ])
        (a2 === Std.list Fun.id [ !!"window"; !!"window"; !!"window"; !!"window" ])
    ]
;;

let delete_day day q =
  match day with
  | Monday -> delete_monday q;
  | Tuesday -> delete_tuesday q;
  | _ -> failure

let using_employ_user u_c q =
  match u_c with
  | "delete_monday" -> delete_monday q
  | "delete_tuesday" -> delete_tuesday q
  | _ -> failure
;;

let rec employ_constraint user_const q =
  match user_const with
  | [] -> success
  | hd :: tl -> using_employ_user hd q &&& employ_constraint tl q
;;
let use_user_constr alg_type q =
  match alg_type with
  | Group_not_learning {number_lesson;day} -> delete_day day q;;

let rec alg_constaint user_constraints q =
  match user_constraints with 
  | [] -> success
  | hd :: tl -> use_user_constr hd q &&& alg_constaint tl q
;;
(* let rec user_constraint user_const q = conde
 [ user_const === nil ()
;
fresh(first last) (user_const === List.cons first last) *)
(* (first q) (last q)] *)
(* ЭТО НУЖНО ЗАМЕТЧИТЬ, ТО ЕСТЬ БЕРЕМ СПИСОК ЦЕЛЕЙ, проверяем, если цель такая то, то вызываем определенную реляцию, смесь функционального программирования и реляционного *)
let reifier () = Std.List.reify (Std.List.reify (Std.List.reify OCanren.reify))

let shower =
  GT.show
    Std.List.logic
    (GT.show
       Std.List.logic
       (GT.show Std.List.logic (GT.show OCanren.logic @@ GT.show GT.string)))
;;

let searcho _constaints answer =
  fresh
    (q r s t)

    (* (employ_constraint [ "delete_monday" ] q) *)
    (alg_constaint _constaints q)
    (answer === Std.list Fun.id [ q; r; s; t ])
    (init_sched_a_week q)
    (init_sched_a_week t)
    (init_sched_a_week r)
    (init_sched_a_week s)
    (sched
       (Std.list
          Fun.id
          [ Std.list Fun.id [ !!"matan1"; !!"matan2"; !!"geom1"; !!"alg1" ]
          ; Std.list Fun.id [ !!"matan3"; !!"matan4"; !!"geom2"; !!"alg2" ]
          ])
       (Std.list Fun.id [ q; r ])
       (Std.list
          Fun.id
          [ Std.list Fun.id [ s; s; s; s ]; Std.list Fun.id [ s; s; s; s ] ])
       (Std.list Fun.id [ t ])
       (Std.list
          Fun.id
          [ Std.list
              Fun.id
              [ !!"matan1"
              ; !!"geom1"
              ; !!"eng1"
              ; !!"matan3"
              ; !!"matan4"
              ; !!"geom2"
              ; !!"alg2"
              ; !!"matan2"
              ; !!"matan6"
              ; !!"geom2"
              ; !!"alg1"
              ]
          ]))
;;

(* у вас есть унификация - работайте *)
(* dbms_random.random *)
