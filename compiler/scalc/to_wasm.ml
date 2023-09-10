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

let bt_ret_eq = Owi.Symbolic.(Arg.Bt_raw (None, ([], [Ref_type (Null, Eq_ht)])))
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
  | Length -> [] (* TODO *)
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
    (* TODO: change the type of block to accept one parameter *)
    (* TODO: make this a proper function to be able to make a recursive call *)
    let x, y = pop2 args in
    let x = expression x in
    let y = expression y in
    (* we store x and y *)
    x @ [ Global_set (Symbolic "tmp_block") ]
    @ y @ [ Global_set (Symbolic "tmp_block2") ]
    (* we start to check if they are null *)
    @ [ Global_get (Symbolic "tmp_block"); Ref_is_null; If_else (None, Some bt_ret_eq, [
      (* x is null, we just need to check if y is null too *)
      Global_get (Symbolic "tmp_block2")
    ; Ref_is_null
    ; I31_new ],
      (* x is not null, we check if it's an i31 *)
      [ Block (Some "eq", Some bt_ret_eq, [
          Block (Some "eq_i31_case", Some bt_ret_eq, [
            Global_get (Symbolic "tmp_block")
          ; Br_on_cast_fail (Symbolic "eq_i31_case", No_null, I31_ht)
          (* x is an i31, let's see if y too *)
          ; Block (Some "eq_i31_case_yes", Some bt_ret_eq, [
            Global_get (Symbolic "tmp_block2")
          ; Br_on_cast_fail (Symbolic "eq_i31_case_yes", No_null, I31_ht)
          (* they both are int, we check if they're equal *)
          ; I31_get_s
          ; I31_get_s
          ; I_relop (S32, Eq)
          ; I31_new
          ; Br (Symbolic "eq")
          ])
          (* y is not an i31, they're not equal *)
          ; I32_const 0l
          ; I31_new
          ; Br (Symbolic "eq")
          ])
        (* x is not an i31, we check if it's a block *)
        ; Block (Some "eq_block_case", Some bt_ret_eq, [
            Global_get (Symbolic "tmp_block")
          ; Br_on_cast_fail (Symbolic "eq_block_case", No_null, Def_ht (Symbolic "block"))
          (* x is a block, let's see if y too *)
          ; Block (Some "eq_block_case_yes", Some bt_ret_eq, [
            Global_get (Symbolic "tmp_block2")
          ; Br_on_cast_fail (Symbolic "eq_block_case_yes", No_null, I31_ht)
          (* they both are block, we check if they're equal *)
          (* TODO: check the tag for a quick failure in case of not equal types, then: *)
          (* TODO: recursive call on all fields *)
          ; Unreachable
          ])
          (* y is not a block, they're not equal *)
          ; I32_const 0l
          ; I31_new
          ; Br (Symbolic "eq")
          ])
        (* something is wrong, they are not null/i31/block and we shouldn't have any other kind of value *)
        ; Unreachable
        ])
      ])
    ]
  | Map -> (* TODO *) []
  | Concat -> assert false
  | Filter -> (* TODO *) []
  (* * overloaded *)
  | Add_int_int -> assert false
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
  | Reduce -> [] (* TODO *)
  | Fold -> assert false
  | HandleDefault -> assert false
  | HandleDefaultOpt -> [] (* TODO *)

and expression e =
  let open Owi.Symbolic in
  match Catala_utils.Mark.remove e with
  | EVar v -> [Local_get (Symbolic (string_of_var v))]
  | EFunc _ -> assert false
  | EStruct (es, _s) ->
    struct_tag
    :: (List.map (expression) es |> List.flatten)
    @ [ Array_new_fixed (Symbolic "block", (1 + List.length es)) ]
  | EStructFieldAccess (e, field, _) ->
    (* TODO: get the field properly *)
    let field = (Obj.magic field) in
    expression e @ [
      Ref_cast (No_null, Def_ht (Symbolic "block"))
    ; Array_get (Raw (1 + field)) ]
  | EInj _ -> [] (* TODO *)
  | EArray es ->
    array_tag
    :: (List.map (expression) es |> List.flatten)
    @ [ Array_new_fixed (Symbolic "block", (1 + List.length es)) ]
  | ELit l -> lit l
  | EApp ((EOp o, _), args) -> op o args
  | EApp _ -> assert false
  | EOp _ -> assert false

let rec statement ctx s =
  match Catala_utils.Mark.remove s with
  | SInnerFuncDef _ ->
    (* as we performed closure conversion, there's no inner function anymore *)
    (* TODO *)
    []
  | SLocalDecl _ -> []
  | SLocalDef (v, e) ->
    expression e
    @ [
      (let open Owi.Symbolic in
        Local_set (Symbolic (string_of_mvar v)));
    ]
  | STryExcept _ -> assert false
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
    ; If_else (None, Some bt_ret_eq, b1, b2)
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
      ; Array_get (Raw 0)
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
              ; Array_get (Raw 1)
              ; Local_set (Symbolic (string_of_var payload_var))
              ] @ block ctx case_block  in
            [ (* if the tag match, we go to the case_code branch, otherwise we try other branches in acc *)
              Global_get (Symbolic "tmp_switch_value")
            ; I32_const tag
            ; I_relop (S32, Eq)
            ; If_else (None, Some bt_ret_eq, case_code, acc)])
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
      If_else (None, None, [ Unreachable ], [])
    ]
and block ctx b = List.map (statement ctx) b |> List.flatten

let collect_locals b =
  List.map Catala_utils.Mark.remove b
  |> List.filter_map (function
    | SLocalDecl (name, _typ) ->
      let name = Some (string_of_mvar name) in
      let typ = Owi.Symbolic.Ref_type (No_null, Eq_ht) in
      Some (name, typ)
    | _ -> None)

let item ctx item : Owi.Symbolic.module_field =
  match item with
  | SVar _ ->
    Format.eprintf "TODO (SVar)@\n";
    assert false
  | SFunc { var = func_name; func }
  | SScope { scope_body_var = func_name; scope_body_func = func; _ } ->
    let func_params = func.func_params in
    let func_body = func.func_body in
    let open Owi.Types in
    let open Owi.Symbolic in
    let id = Some (string_of_func_name func_name) in
    (* we use eqref as a uniform representation for now, later we could propagate more precise types *)
    let params =
      List.map
        (fun (var, _typ) ->
            Some (string_of_mvar var), Ref_type (No_null, Eq_ht))
        func_params
    in
    (* we need to collect the list of locals required by the code to declare them beforehand *)
    let locals = collect_locals func_body in
    let body = block ctx func_body in
    (* each function returns one and exactly one eqref *)
    let type_f = Arg.Bt_raw (None, (params, [Ref_type (No_null, Eq_ht)])) in
    let func = { id; body; locals; type_f } in
    MFunc func

let code_items ctx code_items : Owi.Symbolic.module_field list =
  List.map (item ctx) code_items

let program p : Owi.Symbolic.modul =
  let open Owi.Symbolic in
  let id = Some "catala_module" in
  let fields = [
    (* the type of blocks, it's an array of eqref *)
    MType [ Some "block", (Final, [], Def_array_t (Var, Val_storage_t (Ref_type (Null, Eq_ht)))) ]
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
  Format.fprintf fmt
    ";; This file has been generated by the Catala compiler, do not edit!@\n\n\
     %a"
    Owi.Symbolic.Pp.modul modul
