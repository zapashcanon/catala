(* This file is part of the Catala compiler, a specification language for tax
   and social benefits computation rules. Copyright (C) 2020 Inria, contributor:
   Léo Andrès <contact@ndrs.fr>

   Licensed under the Apache License, Version 2.0 (the "License"); you may not
   use this file except in compliance with the License. You may obtain a copy of
   the License at

   http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
   WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
   License for the specific language governing permissions and limitations under
   the License. *)

open Ast

let string_of_func_name = Format.asprintf "%a" Print.format_func_name
let string_of_var var = Format.asprintf "%a" Print.format_var_name var
let string_of_mvar var = string_of_var (Catala_utils.Mark.remove var)

let bt_ret_eq = Owi.Symbolic.(Arg.Bt_raw (None, ([], [Ref_type (No_null, Eq_ht)])))
let struct_tag = Owi.Symbolic.I32_const 654321l
let array_tag = Owi.Symbolic.I32_const 765432l

let lit =
  let open Owi.Symbolic in
  function
  | Shared_ast.LUnit -> [ I32_const 0l; I31_new ]
  | LBool false -> [ I32_const 0l; I31_new ]
  | LBool true -> [ I32_const 1l; I31_new ]
  | LInt i ->
    (* TODO: proper handling of big numbers *)
    [ I32_const (Z.to_int32 i); I31_new ]
  | LRat _ -> assert false
  | LMoney _ -> assert false
  | LDate _ -> assert false
  | LDuration _ -> assert false

let pop1 = function
  | [ x ] -> x
  | _ -> assert false

let pop2 = function
  | [ x; y ] -> x, y
  | _ -> assert false

let rec collect_locals_block b =
  List.map (fun s -> Catala_utils.Mark.remove s |> collect_locals_statement) b
  |> List.flatten
and collect_locals_statement = function
  | SInnerFuncDef _ -> []
  | SLocalDecl (name, _typ) ->
    let name = Some (string_of_mvar name) in
    let typ = Owi.Symbolic.Ref_type (Null, Eq_ht) in
    [(name, typ)]
  | SLocalDef _ -> []
  | STryExcept (try_block, _, catch_block) ->
    collect_locals_block try_block @ collect_locals_block catch_block
  | SRaise _ -> []
  | SIfThenElse (_, b1, b2) ->
    collect_locals_block b1 @ collect_locals_block b2
  | SSwitch (_, _, cases) ->
    List.map (fun (case_block, payload_var) ->
      let name = Some (string_of_var payload_var) in
      let typ = Owi.Symbolic.Ref_type (No_null, Eq_ht) in
      let v = name, typ in
      let vs = collect_locals_block case_block in
      v :: vs) cases
    |> List.flatten
  | SReturn _ -> []
  | SAssert _ -> []

let rec collect_inner_func_def_item = function
  | SVar _ -> []
  | SFunc { func; _ } | SScope { scope_body_func = func; _ } ->
    collect_inner_func_def_block func.func_body
and collect_inner_func_def_block b =
  List.fold_left (fun acc s -> collect_inner_func_def_statement (Catala_utils.Mark.remove s) @ acc ) [] b
and collect_inner_func_def_statement = function
  | SInnerFuncDef ((var, _typ), func) ->
    (* TODO: convert the varname into a funcname *)
    let var = Obj.magic var in
    let f = SFunc { var; func } in
    let fs = collect_inner_func_def_block func.func_body in
    f :: fs
  | SLocalDecl _ -> []
  | SLocalDef _ -> []
  | STryExcept (try_block, _, catch_block) ->
    collect_inner_func_def_block try_block @ collect_inner_func_def_block catch_block
  | SRaise _ -> []
  | SIfThenElse (_, b1, b2) ->
    collect_inner_func_def_block b1 @ collect_inner_func_def_block b2
  | SSwitch (_, _, cases) ->
    List.map (fun (case_block, _payload_var) ->
      collect_inner_func_def_block case_block) cases
    |> List.flatten
  | SReturn _ -> []
  | SAssert _ -> []


let rec op (op : operator) args =
  let open Owi.Symbolic in
  match op with
  (* * monomorphic *)
  | Shared_ast.Operator.Not -> assert false
  | GetDay -> assert false
  | GetMonth -> assert false
  | GetYear -> assert false
  | FirstDayOfMonth -> assert false
  | LastDayOfMonth -> assert false
  (* * polymorphic *)
  | Length -> assert false
  | Log _ -> assert false
  | ToClosureEnv -> assert false
  | FromClosureEnv -> assert false
  (* * overloaded *)
  | Minus_int -> assert false
  | Minus_rat -> assert false
  | Minus_mon -> assert false
  | Minus_dur -> assert false
  | ToRat_int -> assert false
  | ToRat_mon -> assert false
  | ToMoney_rat -> assert false
  | Round_rat -> assert false
  | Round_mon -> assert false
  (* binary *)
  (* * monomorphic *)
  | And -> assert false
  | Or -> assert false
  | Xor -> assert false
  (* * polymorphic *)
  | Eq ->
    let x, y = pop2 args in
    let x = expression x in
    let y = expression y in
    x @ y @ [ Call (Symbolic "eq") ]
  | Map -> assert false
  | Concat -> assert false
  | Filter -> assert false
  (* * overloaded *)
  | Add_int_int ->
    let x, y = pop2 args in
    let x = expression x in
    let y = expression y in
    x @ [ Ref_cast (No_null, I31_ht); I31_get_s ] @ y @ [ Ref_cast (No_null, I31_ht); I31_get_s; I_binop (S32, Add); I31_new ]
  | Add_rat_rat -> assert false
  | Add_mon_mon -> assert false
  | Add_dat_dur _ -> assert false
  | Add_dur_dur -> assert false
  | Sub_int_int -> assert false
  | Sub_rat_rat -> assert false
  | Sub_mon_mon -> assert false
  | Sub_dat_dat -> assert false
  | Sub_dat_dur -> assert false
  | Sub_dur_dur -> assert false
  | Mult_int_int -> assert false
  | Mult_rat_rat -> assert false
  | Mult_mon_rat -> assert false
  | Mult_dur_int -> assert false
  | Div_int_int -> assert false
  | Div_rat_rat -> assert false
  | Div_mon_rat -> assert false
  | Div_mon_mon -> assert false
  | Div_dur_dur -> assert false
  | Lt_int_int -> assert false
  | Lt_rat_rat -> assert false
  | Lt_mon_mon -> assert false
  | Lt_dat_dat -> assert false
  | Lt_dur_dur -> assert false
  | Lte_int_int -> assert false
  | Lte_rat_rat -> assert false
  | Lte_mon_mon -> assert false
  | Lte_dat_dat -> assert false
  | Lte_dur_dur -> assert false
  | Gt_int_int -> assert false
  | Gt_rat_rat -> assert false
  | Gt_mon_mon -> assert false
  | Gt_dat_dat -> assert false
  | Gt_dur_dur -> assert false
  | Gte_int_int -> assert false
  | Gte_rat_rat -> assert false
  | Gte_mon_mon -> assert false
  | Gte_dat_dat -> assert false
  | Gte_dur_dur -> assert false
  | Eq_int_int -> assert false
  | Eq_rat_rat -> assert false
  | Eq_mon_mon -> assert false
  | Eq_dur_dur -> assert false
  | Eq_dat_dat -> assert false
  (* ternary *)
  (* * polymorphic *)
  | Reduce -> assert false
  | Fold -> assert false
  | HandleDefault -> assert false
  | HandleDefaultOpt ->
    (* TODO: put args on the stack *)
    [ Call (Symbolic "handle_default_opt") ]

and expression e =
  let open Owi.Symbolic in
  match Catala_utils.Mark.remove e with
  | EVar v ->
    let v = string_of_var v in
    (* TODO: this is an horrible hack to replace some dead values by null, otherwise they appear as unbounded *)
    if String.length v >= 10 && String.sub v 0 10 = "dead_value" then [ Call (Symbolic "dead_value") ]
    else
      [Local_get (Symbolic  v); Ref_as_non_null]
  | EFunc _ -> assert false
  | EStruct (es, _s) ->
    struct_tag
    :: I31_new
    :: (List.map (expression) es |> List.flatten)
    @ [ Array_new_fixed (Symbolic "block", (1 + List.length es)) ]
  | EStructFieldAccess (e, field, _) ->
    (* TODO: get the field properly *)
    let field = (Obj.magic field) in
    expression e
    @ [  Ref_cast (No_null, Def_ht (Symbolic "block"))
      ; I32_const (Int32.of_int (1 + field))
      ; Array_get (Symbolic "block") ]
  | EInj (e, _cons, _enum_name) ->
    expression e
    @ [ Ref_cast (No_null, Def_ht (Symbolic "block")) ]
  (* TODO: properly do the injection *)
  | EArray es ->
    array_tag
    :: I31_new
    :: (List.map (expression) es |> List.flatten)
    @ [ Array_new_fixed (Symbolic "block", (1 + List.length es)) ]
  | ELit l -> lit l
  | EApp ((EOp o, _), args) -> op o args
  | EApp _ -> assert false
  | EOp _ -> assert false

let rec statement ctx s =
  match Catala_utils.Mark.remove s with
  | SInnerFuncDef _ -> []
  (* as we performed closure conversion, there's no inner function anymore *)
  (* TODO: actually they still seem to be present, so we extract them with collect_inner_func_def_item
     before and ignore them here... *)
  | SLocalDecl _ ->
    (* they have been collected and added to the function if needed in collect_locals *)
    []
  | SLocalDef (v, e) ->
    let e = expression e in
    let v = string_of_mvar v in
    let v = Owi.Symbolic.Local_set (Symbolic v) in
    e @ [ v ]
  | STryExcept _ ->
    (* we use --avoid_exceptions so we don't have try ... catch block anymore*)
    assert false
  | SRaise _ ->
    (* TODO: fail in a better way *)
    (* we use --avoid_exceptions so this can only be a fatal error *)
    [ Unreachable ]
  | SIfThenElse (cond, b1, b2) ->
    let b1 = block ctx b1 in
    let b2 = block ctx b2 in
    expression cond @ [
      Ref_cast (No_null, I31_ht)
    ; I31_get_u
    ; If_else (Some "ite", Some bt_ret_eq, b1, b2)
    ]
  | SSwitch (e, enum_name, cases) ->
    let open Shared_ast in
    let cons_map = EnumName.Map.find enum_name ctx.ctx_enums in
    let cases =
      List.map2
        (fun (l, r) (cons, _) -> l, r, cons)
        cases
        (EnumConstructor.Map.bindings cons_map)
    in
    let open Owi.Symbolic in
    let e =
      (* the expression we match on *)
      expression e @ [
        (* we store the result of the expression in $tmp_block and its tag in $tmp_switch_value*)
        Ref_cast (No_null, Def_ht (Symbolic "block"))
      ; Global_set (Symbolic "tmp_block")
      ; Global_get (Symbolic "tmp_block")
      ; Ref_as_non_null
      ; I32_const 0l
      ; Array_get (Symbolic "block")
      ; Ref_cast (No_null, I31_ht)
      ; I31_get_u
      ; Global_set (Symbolic "tmp_switch_value") ;
      ] in
    let switch =
      List.fold_left
        (fun acc ((case_block : block), payload_var, cons_name) ->
            (* TODO: properly get an int *)
            let tag = Int32.of_int (Obj.magic cons_name) in
            let case_code =
              [ (* the block has a single parameter,
                   we need to bind payload_var to it before entering the case_block *)
                Global_get (Symbolic "tmp_block")
              ; Ref_as_non_null
              ; I32_const 1l
              ; Array_get (Symbolic "block")
              ; Local_set (Symbolic (string_of_var payload_var))
              ] @ block ctx case_block  @ [
                (* returns unit *)
                I32_const 0l;
                I31_new
              ] in
            [ (* if the tag match, we go to the case_code branch, otherwise we try other branches in acc *)
              Global_get (Symbolic "tmp_switch_value")
            ; I32_const tag
            ; I_relop (S32, Eq)
            ; If_else (Some "switch", Some bt_ret_eq, case_code, acc)])
        (* Unreachable is the last branch we'll try,
           this happen when we've got a match failure,
           this should not happen in correctly typechecked code but Wasm doesn't know this... *)
        [Unreachable] cases
    in
    e @ switch
  | SReturn e -> expression (e, Catala_utils.Mark.get s) @ [Owi.Symbolic.Return]
  | SAssert e ->
    let open Owi.Symbolic in
    expression (e, Catala_utils.Mark.get s) @ [
      Ref_cast (No_null, I31_ht);
      I31_get_u;
      I32_const 0l;
      I_relop (S32, Eq);
      (* TODO: fail in a better way *)
      If_else (Some "assert", None, [ Unreachable ], [])
    ]
and block ctx b = List.map (statement ctx) b |> List.flatten

and item ctx = function
  | SVar _ ->
    Format.eprintf "TODO (SVar)@\n";
    assert false
  | SFunc { var = func_name; func }
  | SScope { scope_body_var = func_name; scope_body_func = func; _ } as i->
    let func_params = func.func_params in
    let func_body = func.func_body in
    let open Owi.Types in
    let open Owi.Symbolic in
    let id = Some (string_of_func_name func_name) in
    (* we use eqref as a uniform representation for now, later we could propagate more precise types *)
    let params =
      List.map
        (fun (var, _typ) ->
            Some (string_of_mvar var), Ref_type (Null, Eq_ht))
        func_params
    in
    (* we need to collect the list of locals required by the code to declare them beforehand *)
    let locals = collect_locals_block func_body in
    let body = block ctx func_body in
    (* we need to collect the inner functions and to lift them outside *)
    let inner_funcs = collect_inner_func_def_item i |> List.map (item ctx) |> List.flatten in
    (* each function returns one and exactly one eqref *)
    let type_f = Arg.Bt_raw (None, (params, [Ref_type (No_null, Eq_ht)])) in
    let func = { id; body; locals; type_f } in
    MFunc func :: inner_funcs

let code_items ctx code_items : Owi.Symbolic.module_field list =
  List.map (item ctx) code_items |> List.flatten

let program p : Owi.Symbolic.modul =
  let open Owi.Symbolic in
  let id = Some "catala_module" in
  let fields = [
    (* runtime funcs *)
    MImport { modul = "catala_runtime"; name = "dead_value"; desc = Import_func (Some "dead_value", (Owi.Symbolic.Arg.Bt_raw (None,
      ([], [ Ref_type (No_null, Eq_ht) ])))) }
  ;  MImport { modul = "catala_runtime"; name = "eq"; desc = Import_func (Some "eq", (Owi.Symbolic.Arg.Bt_raw (None,
      ([ None, Ref_type (No_null, Eq_ht);  None, Ref_type (No_null, Eq_ht) ], [ Ref_type (No_null, Eq_ht) ])))) }
  ; MImport { modul = "catala_runtime"; name = "handle_default_opt"; desc = Import_func (Some "handle_default_opt", bt_ret_eq) }
  (* the type of blocks, it's an array of eqref *)
  ; MType [ Some "block", (Final, [], Def_array_t (Var, Val_storage_t (Ref_type (No_null, Eq_ht)))) ]
  (* some temporary registers *)
  ; MGlobal {
    id = Some "tmp_switch_value"
  ; typ = Var, Num_type I32
  ; init = [ I32_const 666l ] }
  ; MGlobal {
    id = Some "tmp_block"
  ; typ = Var, Ref_type (Null, (Def_ht (Symbolic "block")))
  ; init = [ Ref_null (Def_ht (Symbolic "block")) ]
  }
  ; MGlobal {
    id = Some "tmp_block2"
  ; typ = Var, Ref_type (Null, (Def_ht (Symbolic "block")))
  ; init = [ Ref_null (Def_ht (Symbolic "block")) ]
  }]
    (* fields from the program *)
    @ code_items p.decl_ctx p.code_items in
  { id; fields }

let format_program
    (fmt : Format.formatter)
    (p : Ast.program)
    (_type_ordering : Scopelang.Dependency.TVertex.t list) : unit =
  let modul = program p in
  Owi.Symbolic.Pp.modul fmt modul
