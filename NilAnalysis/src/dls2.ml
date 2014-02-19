open Cfg
open Cfg_printer
open Visitor
open Utils
open Cfg_refactor
open Cfg_printer .CodePrinter
open Printf
  
(* INIZIO CONTRACT LIVENESS *)
  
module LivenessAnalysis = struct
  
  type fact = Live | Dead
    
  let fact_to_s = function Live -> "Live" | Dead -> "Dead"
    
  let top = StrMap.empty
  type t = fact StrMap.t
  let empty = StrMap.empty
  let eq t1 t2 = StrMap.compare Pervasives.compare t1 t2 = 0 
  let to_string t = strmap_to_string fact_to_s t
    
				
  let meet_fact t1 t2 = match t1,t2 with	
    | _, Live ->  print_string "confronto \n"; Live			
    | _, Dead -> print_string "confronto \n"; Dead
      
  let meet_fact_IF t1 t2 = match t1,t2 with	
    | _, Live ->  print_string "confronto \n"; Live			
    | Live, _ -> print_string "confronto \n"; Live
    | Dead, Dead -> print_string "confronto \n"; Dead
      
  let update s v map =
    let fact =
      try meet_fact (StrMap.find s map) v
      with Not_found -> v
    in 
    StrMap.add s fact map	
      
  let update_IF s v map =
    let fact =
      try meet_fact_IF (StrMap.find s map) v
      with Not_found -> v
    in 
    StrMap.add s fact map	
      
  let join lst =		(*join receives a list of StrMap (String, fact) *) 
    print_string "joinnnnnnn \n" ; 
   	if (List.length lst) > 1 then
      let map1 = (fun acc map -> StrMap.fold update_IF map acc) (List.nth lst 0) (List.nth lst 1) in
      let map2 = (fun acc map -> StrMap.fold update_IF map acc) (List.nth lst 1) (List.nth lst 0) in
      (fun acc map -> StrMap.fold update_IF map acc) map1 map2		(* now map1 and map2 are defined on the same set of variables *)
    else
      List.fold_left (fun acc map ->
        StrMap.fold update map acc) StrMap.empty lst
        
  let rec update_lhs fact map lhs = match lhs with
    | `ID_Var(`Var_Local, var) -> update var fact map
    | `ID_Var(`Var_Constant, const) -> update const fact map
    | #identifier -> map
    | `Tuple lst -> List.fold_left (update_lhs Dead) map lst
    | `Star (#lhs as l) -> update_lhs Dead map l
      
  let update_use lhs value map =
    let map = update_lhs Dead map lhs 
    in
      let map = update value Live map 
    in map
      
  let rec transfer map stmt = match stmt.snode with

    | Assign(lhs , #literal) | Assign(lhs , `ID_True) | Assign(lhs , `ID_False) -> print_string "true false literal\n"; update_lhs Dead map lhs
    | Assign(lhs , `ID_Nil) -> print_string "null\n"; update_lhs Dead map lhs
    | Assign(lhs, `ID_Var(`Var_Local, rvar)) ->  print_string "var\n"; update_use lhs rvar map
    | Assign(lhs, `ID_Var(`Var_Constant, rconst)) ->  print_string "constant\n";update_use lhs rconst map
    
    | MethodCall(lhs_o, {mc_target=Some (`ID_Var(`Var_Local, targ)); mc_args = par} ) 
    | MethodCall(lhs_o, {mc_target=Some (`ID_Var(`Var_Constant, targ)); mc_args = par} ) -> 
      let map = match lhs_o with
      | None -> update targ Live map
      | Some lhs -> update_use lhs targ map
    in map

   (* DA AGGIUNGERE UPDATE PARAMETRI E TOGLIERE QUELLO CHE NON SERVE 

   | MethodCall(lhs_o, {mc_target=Some #literal; mc_args = par} ) -> 
      let map = match lhs_o with
      | None -> update "test" Live map
      | Some lhs -> update_use lhs "targ" map
    in map *)

    | MethodCall(lhs_o, {mc_target=Some s; mc_args = par} ) -> 
      let map = match lhs_o with
      | None -> map
      | Some lhs -> update_lhs Dead map lhs 
    in map

    (* | MethodCall(lhs_o, {mc_target=Some (`ID_Var(`Var_Local, targ)); mc_args = par}) ->
       print_string "aijiaji\n";

       List.iter (fun x ->  match x with
                            | None -> print_string "none\n"
                            (* | Some (`Lit_Array, targ) -> print_string "var \n" *)
                ) par;

     	let map = match lhs_o with
        | None -> update targ Live map
        (* QUIIII | Some (`ID_Var(`Var_Local, t)) -> print_string "questo caso\n";*)
        | Some lhs -> update_use lhs targ map (* to be updated! *)
      in
      map (*get_fact targ map StrMap.add targ NonNil map*) *)
    (* | Assign(lhs, MethodCall(lhs_o, {mc_target=Some (`ID_Var(`Var_Local, targ))})) -> update_use lhs targ map *)
    (* | MethodCall(Some lhs, _ ) -> print_string "tutto il resto\n"; update_lhs Dead map lhs ; *)
      
    | _ -> map 
      
end

(* FINE CONTRACT LIVENESS *)

module NilAnalysis = struct
  type fact = MaybeNil | NonNil
    
  let fact_to_s = function MaybeNil -> "MaybeNil" | NonNil -> "NonNil"
    
  let meet_fact_IF t1 t2 = match t1,t2 with
    | MaybeNil, _ 
    | _, MaybeNil -> MaybeNil
    | NonNil, NonNil -> NonNil
      
  let meet_fact t1 t2 = match t1,t2 with	
    | _, NonNil -> NonNil
    | _, MaybeNil -> MaybeNil
      
  let update s v map =
    let fact =
      try meet_fact (StrMap.find s map) v
      with Not_found -> v
    in
    StrMap.add s fact map (* this instruction returns a new map! it does not modify ifacts *)
      
  let updateIF s v map =
    let fact =
      try meet_fact_IF (StrMap.find s map) v
      with Not_found -> MaybeNil
    in 
    StrMap.add s fact map
      
  let join lst =		(*join receives a list of StrMap (String, fact) *) 	
   	if (List.length lst) > 1 then
      let map1 = (fun acc map -> StrMap.fold updateIF map acc) (List.nth lst 0) (List.nth lst 1) in
      let map2 = (fun acc map -> StrMap.fold updateIF map acc) (List.nth lst 1) (List.nth lst 0) in
      (fun acc map -> StrMap.fold updateIF map acc) map1 map2		(* now map1 and map2 are defined on the same set of variables *)
    else
      List.fold_left (fun acc map ->
        StrMap.fold update map acc) StrMap.empty lst
        
 	type t = fact StrMap.t
  let empty = StrMap.empty
  let eq t1 t2 = StrMap.compare Pervasives.compare t1 t2 = 0 
  let to_string t = strmap_to_string fact_to_s t
    
  let rec update_lhs fact map lhs = match lhs with
    | `ID_Var(`Var_Local, var) -> update var fact map
    | `ID_Var(`Var_Constant, const) -> update const fact map
    | #identifier -> map
    | `Tuple lst -> List.fold_left (update_lhs MaybeNil) map lst
    | `Star (#lhs as l) -> update_lhs NonNil map l
      
  let transfer map stmt = match stmt.snode with
    | Assign(lhs , #literal) | Assign(lhs , `ID_True) | Assign(lhs , `ID_False) -> update_lhs NonNil map lhs
    | Assign(lhs , `ID_Nil) -> update_lhs MaybeNil map lhs
    | Assign(lhs, `ID_Var(`Var_Local, rvar)) -> update_lhs (StrMap.find rvar map) map lhs
    | Assign(lhs, `ID_Var(`Var_Constant, rconst)) -> update_lhs (StrMap.find rconst map) map lhs
    | MethodCall(lhs_o, {mc_target=Some (`ID_Var(`Var_Local, targ))}) ->
     	let map = match lhs_o with
        | None -> map
        | Some lhs -> update_lhs MaybeNil map lhs (* to be updated! *)
      in
      map (*get_fact targ map StrMap.add targ NonNil map*)
    | Class(Some lhs, _ , _ ) 
    | Module(Some lhs, _ , _ )
    | MethodCall(Some lhs, _ )
    | Yield(Some lhs, _ )
    | Assign(lhs, _ ) -> update_lhs MaybeNil map lhs
      
    | _ -> map             
end

(* INIZIO MODULO LIVENESS *)

module Liveness = Dataflow.Backwards(LivenessAnalysis)
  
		let print_pos node pos =
    print_string "[WARNING]: Dead var: \n in method call "; print_stmt stdout node; 
    Printf.printf " at %s:%d \n"
      pos.Lexing.pos_fname pos.Lexing.pos_lnum; 
    flush_all () 
  (* Printf.printf "[WARNING]: MaybeNil dereference in %s at line %d \n" *)
  (* pos.Lexing.pos_fname pos.Lexing.pos_lnum; *)
  (* flush_all () *)
      
  let refactor targ node =
    let nodee = freparse ~env:node.lexical_locals
      "unless %a.nil? then %a end" format_expr targ format_stmt node
    in ChangeTo nodee
      
  let print_warning node =
    print_pos node node.pos;
  (* print_stmt stdout node *)
    
  class analizeLivenes ifs = object(s)		(* safeNil visitor *)
    inherit default_visitor as super
    val facts = ifs
      
    method visit_stmt node = match node.snode with 
      | Method(mname, args, body) -> 
        print_string "Method definition: \n";
        let in', out' = Liveness.fixpoint body in
        s#print_hash (in', out');
        print_string "\n--------------------------------------------\n";
        let me = {<facts = in'>} in
        let body' = visit_stmt (me:>cfg_visitor) body in
       	ChangeTo (update_stmt node (Method(mname, args, body')))
          
      | MethodCall( _ , {mc_target=(Some `ID_Self|None)}) -> SkipChildren
        
      | MethodCall( _ , {mc_target=Some (`ID_Var(`Var_Local, var) as targ)}) ->  print_string "testttttttt \n" ; print_string var ; print_string "\n"; print_stmt stdout node; print_string "\n";  
        begin try let map = Hashtbl.find facts node in 
          begin try match StrMap.find var map with
            | LivenessAnalysis.Dead -> print_warning node; refactor targ node
            | LivenessAnalysis.Live -> SkipChildren
                with Not_found ->  print_warning node; refactor targ node
          end
              with Not_found -> print_string "Assert false occurred in stmt: \n"; print_stmt stdout node; assert false
        end
        
      | MethodCall( _ , {mc_target=Some (`ID_Var(`Var_Constant, const) as targ)}) ->
        begin try let map = Hashtbl.find facts node in 
          begin try match StrMap.find const map with
            | LivenessAnalysis.Dead -> print_warning node; refactor targ node
            | LivenessAnalysis.Live -> SkipChildren
                with Not_found ->  print_warning node; refactor targ node
          end
              with Not_found -> print_string "Assert false occurred in stmt: \n"; print_stmt stdout node; assert false
        end
        
      | MethodCall(_, {mc_target=Some (#expr)}) -> SkipChildren  (* print_string "expr\n"; print_stmt stdout node; *)  (* (as targ) refactor targ node*)
      (* | MethodCall(_, _) -> SkipChildren *) 
        
      | _ -> super#visit_stmt node
        
    method print_hash (ifs, ofs) = 
      Hashtbl.iter (fun k v -> 
        (*print_string "Statement: \n";*)
        print_string "\n";
        print_stmt stdout k;
        print_string(" ->  ");
        if (StrMap.is_empty v == false) then
          StrMap.iter (
                       fun k w -> 
                         print_string "(";
                         print_string k;
                         print_string ", ";
                         match w with
                           | LivenessAnalysis.Dead -> print_string "Dead) "
                           | LivenessAnalysis.Live -> print_string "Live) "
                      ) v 
        else
          print_string "\n";
                   ) ifs
        
  end
  
  let print_hash _fs = 
    (*let num1 = Hashtbl.length ifs in
       let num2 = Hashtbl.length ofs in
       print_int(num1);print_string(" - ");print_int(num2);*)
    Hashtbl.iter (fun k v -> 
      (*print_string "Statement: \n";*)
      print_stmt stdout k;
      print_string(" ->  ");
      if (StrMap.is_empty v == false) then
       	StrMap.iter (
                     fun k w -> 
                       print_string "(";
                       print_string k;
                       print_string ", ";
                       match w with
                         | LivenessAnalysis.Dead -> print_string "Dead)\n "
                         | LivenessAnalysis.Live -> print_string "Live)\n "
                    ) v 
      else
        print_string "\n";
      
      print_string "\n";
      
                 ) _fs
;;

let main fname =
  let loader = File_loader.create File_loader.EmptyCfg [] in
  let s = File_loader.load_file loader fname in
  let () = compute_cfg s in
  let () = compute_cfg_locals s in
  print_string "RIL transformed code: \n"; 
  print_stmt stdout s; 
  
  (* ALE *)
  print_int s.pos.Lexing.pos_lnum;
  (**)
  
  print_string "\n---------------------------------------------\n\n";
  let ifs, ofs = Liveness.fixpoint s in
  print_string "-------------------------------------------\n"; 
  print_string "ifs content: \n"; 
  print_hash ifs; 
  print_string "-------------------------------------------\n"; 
  print_string "ofs content: \n"; 
  print_hash ofs; 
  print_string "--------------------------------------------\n";  
  let sn = ( new analizeLivenes ifs :> cfg_visitor ) in
  let _ = visit_stmt (sn) s in
  (* print_string "Transformed code: \n"; *)
  (* CodePrinter.print_stmt stdout ss *)
  (* print_string "--------------------------------------------\n"; *)
  (* print_string "Output code: \n"; *)
  (* ErrorPrinter.print_stmt stdout ss *)
  Printf.printf("\n---------------------------------------------\n");
  print_endline "Nilness analysis complete.\n"
    
let _ = 
  if (Array.length Sys.argv) != 2 
  then begin
    Printf.eprintf "Usage: print_cfg <ruby_file> \n";
    exit 1
  end;
  let fname = Sys.argv.(1) in
  main fname;
  ()
    
(* FINE MODULO LIVENESS *)
    
    
    
let print_hash _fs = 
  (*let num1 = Hashtbl.length ifs in
     let num2 = Hashtbl.length ofs in
     print_int(num1);print_string(" - ");print_int(num2);*)
  Hashtbl.iter (fun k v -> 
    (*print_string "Statement: \n";*)
    print_stmt stdout k;
    print_string(" ->  ");
    if (StrMap.is_empty v == false) then
      StrMap.iter (
                   fun k w -> 
                     print_string "(";
                     print_string k;
                     print_string ", ";
                     match w with
                       | NilAnalysis.MaybeNil -> print_string "MaybeNil)\n"
                       | NilAnalysis.NonNil -> print_string "NonNil)\n"
                  ) v 
    else
      print_string "\n";
				
    print_string "\n";
    
               ) _fs
;;

