open Gil_syntax

module Make (S : MyMonadicSMemory.S) : MyMonadicSMemory.S = struct
  include S

  let log =
    Logging.tmi ?title:(Some "State Log")
      ?severity:(Some Logging.Logging_constants.Severity.Log)

  let execute_action action s args =
    log (fun f ->
        f "Executing action %s with args [%a]" (action_to_str action)
          (Fmt.list ~sep:Fmt.comma Expr.pp)
          args);
    execute_action action s args

  let consume core_pred s args =
    log (fun f ->
        f "Consuming predicate %s with args [%a]" (pred_to_str core_pred)
          (Fmt.list ~sep:Fmt.comma Expr.pp)
          args);
    consume core_pred s args

  let produce core_pred s args =
    log (fun f ->
        f "Producing predicate %s with args [%a]" (pred_to_str core_pred)
          (Fmt.list ~sep:Fmt.comma Expr.pp)
          args);
    produce core_pred s args
end
