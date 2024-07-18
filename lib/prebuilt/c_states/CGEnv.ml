open Gillian.Monadic
module DR = Delayed_result
open Gil_syntax
module Global_env = Cgil_lib.Global_env

(* GEnv State *)
module M : States.MyMonadicSMemory.S = struct
  type t = Global_env.t [@@deriving yojson]
  type err_t = unit [@@deriving show, yojson]
  type action = GetDef
  type pred = unit

  let pp = Global_env.pp

  let action_from_str = function
    | "getdef" -> Some GetDef
    | _ -> None

  let action_to_str GetDef = "getdef"
  let pred_from_str _ = None
  let pred_to_str () = failwith "No pred in GEnv"
  let init_data = ref Global_env.empty

  let init data =
    match Global_env.of_yojson data with
    | Ok g -> init_data := g
    | Error e -> failwith ("Error when initialising C GEnv: " ^ e)

  let empty = !init_data

  (* Execute action *)
  let execute_action GetDef s args =
    match args with
    | [ (Expr.Lit (Loc loc) | Expr.ALoc loc | Expr.LVar loc) ] -> (
        Fmt.pr "State: %a\n" Global_env.pp !init_data;
        match Global_env.find_def_opt s loc with
        | Some def ->
            let v = Global_env.serialize_def def in
            DR.ok (s, [ Expr.Lit (Loc loc); Expr.Lit v ])
        | None ->
            (* If we can't find a function, in UX mode we give up, while in OX mode we
               signal. *)
            if !Gillian.Utils.Config.under_approximation then Delayed.vanish ()
            else
              Fmt.failwith "execute_genvgetdef: couldn't find %s\nGENV:\n%a" loc
                Global_env.pp s)
    | _ -> failwith "Invalid arguments for GetDef"

  let consume () _ _ = failwith "Invalid C GEnv consume"
  let produce () _ _ = failwith "Invalid C GEnv produce"
  let compose _ _ = Delayed.vanish () (* TODO *)
  let is_fully_owned _ _ = Formula.False
  let is_empty _ = false
  let is_concrete _ = false
  let instantiate _ = (Global_env.empty, [])

  (* Core predicates: pred * ins * outs, converted to Asrt.GA *)
  let assertions _ = []
  let assertions_others _ = []
  let can_fix () = false
  let get_fixes () = []
  let lvars _ = Gillian.Utils.Containers.SS.empty
  let alocs _ = Gillian.Utils.Containers.SS.empty
  let substitution_in_place _ s = Delayed.return s
  let get_recovery_tactic _ _ = Gillian.General.Recovery_tactic.none
  let list_actions () = [ (GetDef, [], []) ]
  let list_preds () = []
end
