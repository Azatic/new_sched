open OCanren
open OCanren.Std

let init_sched_one_day s =
  conde [ fresh (q w e r) (s === Std.list Fun.id [ q; w; e; r ]) ]
;;

let rec membero x l = conde [ List.caro l x; fresh d (List.cdro l d) (membero x d) ]

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
