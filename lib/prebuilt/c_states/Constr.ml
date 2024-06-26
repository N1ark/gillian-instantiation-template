open Gil_syntax

module Core = struct
  open LActions

  let pred ga ins outs = (ga, ins, outs)

  let single ~ofs ~chunk ~sval ~perm =
    let chunk = Expr.Lit (String (ValueTranslation.string_of_chunk chunk)) in
    let perm =
      Expr.Lit (String (ValueTranslation.string_of_permission_opt perm))
    in
    pred Single [ ofs; chunk ] [ sval; perm ]

  let array ~ofs ~chunk ~size ~sval_arr ~perm =
    let chunk = Expr.Lit (String (ValueTranslation.string_of_chunk chunk)) in
    let perm =
      Expr.Lit (String (ValueTranslation.string_of_permission_opt perm))
    in
    pred Array [ ofs; size; chunk ] [ sval_arr; perm ]

  let hole ~low ~high ~perm =
    let perm =
      Expr.Lit (String (ValueTranslation.string_of_permission_opt perm))
    in
    pred Hole [ low; high ] [ perm ]

  let zeros ~low ~high ~perm =
    let perm = Expr.string (ValueTranslation.string_of_permission_opt perm) in
    pred Zeros [ low; high ] [ perm ]

  let bounds ~low ~high =
    let bounds = Expr.EList [ low; high ] in
    pred Bounds [] [ bounds ]

  let freed = pred Freed [] []
end

module Others = struct
  open CConstants

  let pred name params = Asrt.Pred (name, params)

  let malloced_abst ~ptr ~total_size =
    pred Internal_Predicates.malloced [ ptr; total_size ]

  let malloced ~ptr ~total_size =
    let loc, ofs = ptr in
    let size = Expr.int_z total_size in
    pred Internal_Predicates.malloced [ Expr.list [ loc; ofs ]; size ]

  let zeros_ptr_size ~ptr ~size =
    pred Internal_Predicates.zeros_ptr_size [ ptr; size ]

  let undefs_ptr_size ~ptr ~size =
    pred Internal_Predicates.undefs_ptr_size [ ptr; size ]

  let array_ptr ~ptr ~chunk ~size ~content =
    let chunk_str = Expr.string (Chunk.to_string chunk) in
    pred Internal_Predicates.array_ptr [ ptr; size; chunk_str; content ]

  let ptr_add ~ptr ~to_add ~res =
    pred Internal_Predicates.ptr_add [ ptr; to_add; res ]
end
