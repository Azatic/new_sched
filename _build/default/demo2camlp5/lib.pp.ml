open OCanren

module Lam =
  struct
    type ('varname, 'self) t =
        V of 'varname
      | App of 'self * 'self
      | Abs of 'varname * 'self
    class virtual ['ivarname, 'varname, 'svarname, 'iself, 'self, 'sself, 'inh, 'extra, 'syn] t_t  =
      object
        method virtual c_V : 'inh -> 'extra -> 'varname -> 'syn
        method virtual c_App : 'inh -> 'extra -> 'self -> 'self -> 'syn
        method virtual c_Abs : 'inh -> 'extra -> 'varname -> 'self -> 'syn
      end
    let gcata_t
        (tr :
         (_, 'typ0__006_, _, _, 'typ1__007_, _, _, ('typ0__006_, 'typ1__007_) t, _)
           #t_t)
        inh subj =
      match subj with
        V _x__001_ -> tr#c_V inh subj _x__001_
      | App (_x__002_, _x__003_) -> tr#c_App inh subj _x__002_ _x__003_
      | Abs (_x__004_, _x__005_) -> tr#c_Abs inh subj _x__004_ _x__005_
    class ['varname, 'varname_2, 'self, 'self_2, 'extra_t, 'syn_t] gmap_t_t fvarname
        fself _fself_t =
      object
        inherit
          [unit, 'varname, 'varname_2, unit, 'self, 'self_2, unit, 'extra_t,
          ('varname_2, 'self_2) t]
            t_t
        constraint 'extra_t = ('varname, 'self) t
        constraint 'syn_t = ('varname_2, 'self_2) t
        method c_V () _ _x__008_ = V (fvarname () _x__008_)
        method c_App () _ _x__009_ _x__010_ =
          App (fself () _x__009_, fself () _x__010_)
        method c_Abs () _ _x__011_ _x__012_ =
          Abs (fvarname () _x__011_, fself () _x__012_)
      end
    let gmap_t fvarname fself inh0 subj =
      GT.transform_gc gcata_t ((new gmap_t_t) fvarname fself) inh0 subj
    class ['varname, 'self, 'extra_t] show_t_t fvarname fself _fself_t =
      object
        inherit
          [unit, 'varname, string, unit, 'self, string, unit, 'extra_t,
          string]
            t_t
        constraint 'extra_t = ('varname, 'self) t
        method c_V () _ _x__013_ =
          let () = () in Printf.sprintf "V (%s)" (fvarname () _x__013_)
        method c_App () _ _x__014_ _x__015_ =
          let () = () in
          Printf.sprintf "App (%s, %s)" (fself () _x__014_)
            (fself () _x__015_)
        method c_Abs () _ _x__016_ _x__017_ =
          let () = () in
          Printf.sprintf "Abs (%s, %s)" (fvarname () _x__016_)
            (fself () _x__017_)
      end
    let show_t fvarname fself inh0 subj =
      GT.transform_gc gcata_t ((new show_t_t) fvarname fself) inh0 subj
    let t =
      {GT.gcata = gcata_t; GT.fix = (fun eta -> GT.transform_gc gcata_t eta);
       GT.plugins =
         object (_)
           method gmap fvarname fself subj =
             gmap_t (GT.lift fvarname) (GT.lift fself) () subj
           method show fvarname fself subj =
             show_t (GT.lift fvarname) (GT.lift fself) () subj
         end}
    let gmap_t fvarname fself subj =
      gmap_t (GT.lift fvarname) (GT.lift fself) () subj
    let show_t fvarname fself subj =
      show_t (GT.lift fvarname) (GT.lift fself) () subj
    type ground = (GT.string, ground) t
    class virtual ['inh, 'extra, 'syn] ground_t =
      object
        inherit
          [GT.string, GT.string, GT.string, ground, ground, ground, 'inh,
          'extra, 'syn]
            t_t
      end
    let gcata_ground = gcata_t
    class ['extra_ground] show_ground_t _fself_ground =
      object
        inherit [unit, 'extra_ground, string] ground_t
        constraint 'extra_ground = ground
        inherit
          [GT.string, ground, 'extra_ground] show_t_t
            (fun () subj -> GT.show GT.string subj)
            _fself_ground
            _fself_ground
      end
    let rec show_ground () subj =
      GT.show t ((fun () subj -> GT.show GT.string subj) ()) (show_ground ())
        subj
    let ground =
      {GT.gcata = gcata_ground;
       GT.fix = (fun eta -> GT.transform_gc gcata_ground eta);
       GT.plugins = object (_) method show subj = show_ground () subj end}
    let show_ground subj = show_ground () subj
    type logic = (GT.string OCanren.logic, logic) t OCanren.logic
    class virtual ['inh, 'extra, 'syn] logic_t =
      object
        inherit
          [(GT.string OCanren.logic, logic) t,
          (GT.string OCanren.logic, logic) t,
          (GT.string OCanren.logic, logic) t, 'inh, 'extra, 'syn]
            OCanren.logic_t
      end
    let gcata_logic = OCanren.gcata_logic
    class ['extra_logic] show_logic_t _fself_logic =
      object
        inherit [unit, 'extra_logic, string] logic_t
        constraint 'extra_logic = logic
        inherit
          [(GT.string OCanren.logic, logic) t, 'extra_logic]
            OCanren.show_logic_t
            (fun () subj ->
               GT.show t
                 ((fun () subj ->
                     GT.show OCanren.logic
                       ((fun () subj -> GT.show GT.string subj) ()) subj)
                    ())
                 (_fself_logic ()) subj)
            _fself_logic
      end
    let rec show_logic () subj =
      GT.show OCanren.logic
        ((fun () subj ->
            GT.show t
              ((fun () subj ->
                  GT.show OCanren.logic
                    ((fun () subj -> GT.show GT.string subj) ()) subj)
                 ())
              (show_logic ()) subj)
           ())
        subj
    let logic =
      {GT.gcata = gcata_logic;
       GT.fix = (fun eta -> GT.transform_gc gcata_logic eta);
       GT.plugins = object (_) method show subj = show_logic () subj end}
    let show_logic subj = show_logic () subj
    type injected = (GT.string ilogic, injected) t OCanren.ilogic
    let v name = inj (V name)
    let app f x = inj (App (f, x))
    let abs f x = inj (Abs (f, x))
    let fmapt fa fb subj =
      let open Env.Monad in
      ((Env.Monad.return (GT.gmap t) <*> fa) <*> fb) <*> subj
    let (reify : (injected, logic) Reifier.t) =
      let open Env.Monad in
      Reifier.fix
        (fun self ->
           OCanren.reify <..>
             chain
               (Reifier.zed (Reifier.rework ~fv:(fmapt OCanren.reify self))))
    let (prj_exn : (injected, ground) Reifier.t) =
      let open Env.Monad in
      Reifier.fix
        (fun self -> OCanren.prj_exn <..> chain (fmapt OCanren.prj_exn self))
    let varX = !!"x"
    let varY = !!"y"
    let varF = !!"f"
  end
