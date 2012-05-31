open Printf
open Cfg
open Cfg_printer
open Cfg_refactor
open Cfg_printer.CodePrinter
open Visitor
open Utils

let method_formal_name = function
	| `Formal_meth_id var
	| `Formal_amp var
	| `Formal_star var
	| `Formal_default(var, _) -> var

module NilAnalysis = struct
	
	type t = fact StrMap.t
	and fact = MaybeNil | NonNil
	
	let top = StrMap.empty
	let eq t1 t2 = StrMap.compare Pervasives.compare t1 t2 = 0
	let fact_to_s = function MaybeNil -> "MaybeNil" | NonNil -> "NonNil"
	let to_string t = strmap_to_string fact_to_s t
	
	let print_map v =  StrMap.iter (
                                fun k w -> 
                                        print_string "(";
                                        print_string k;
                                        print_string ", ";
                                        match w with
                                        | MaybeNil -> print_string "MaybeNil) "
                                        | NonNil -> print_string "NonNil) "
                        ) v 
												
												
	
	
	let meet_fact2 t1 t2 = print_string "MEET_FACT2 ";print_string(fact_to_s t1);print_string(fact_to_s t2);print_string("\n");match t1, t2 with
		| MaybeNil, _ 
		| _, MaybeNil -> MaybeNil
		| NonNil, NonNil -> NonNil

	let meet_fact t1 t2 = print_string "MEET_FACT ";print_string(fact_to_s t1);print_string(fact_to_s t2);print_string("\n");match t1, t2 with
		| _, MaybeNil -> MaybeNil
		| _, NonNil -> NonNil
	
	let update s v map =
		let fact =
			try meet_fact (StrMap.find s map) v
			with Not_found -> v
		in 
		print_string "UPDATE ";
		print_string s;
		print_string " -> ";
		print_string (fact_to_s v);
		print_string "\n";
		StrMap.add s fact map
		
	let update2 s v map =
		let fact =
			try meet_fact2 (StrMap.find s map) v
			with Not_found -> MaybeNil
		in 
		print_string "UPDATE2 ";
		print_string s;
		print_string " -> ";
		print_string (fact_to_s v);
		print_string "\n";
		StrMap.add s fact map
	
	let join lst =
		if (List.length lst)>1 then
			let map1 = (fun acc map -> StrMap.fold update2 map acc) (List.nth lst 0) (List.nth lst 1) in
			let map2 = (fun acc map -> StrMap.fold update2 map acc) (List.nth lst 1) (List.nth lst 0) in
				(fun acc map -> StrMap.fold update2 map acc) map1 map2
		else 
			List.fold_left (fun acc map -> StrMap.fold update map acc) StrMap.empty lst
	
	let rec update_lhs fact map lhs = match lhs with
		| `ID_Var(`Var_Local, var) -> update var fact map
		| `ID_Var(`Var_Constant, var) -> update var fact map
		| #identifier -> map
		| `Tuple lst -> List.fold_left (update_lhs MaybeNil) map lst
		| `Star (#lhs as l) -> update_lhs NonNil map l
	
	let transfer map stmt = match stmt.snode with
		| Assign(lhs, #literal) | Assign(lhs, `ID_True) | Assign(lhs, `ID_False) -> update_lhs NonNil map lhs
		| Assign(lhs, `ID_Var(`Var_Local, rvar)) -> update_lhs (StrMap.find rvar map) map lhs
		| Assign(lhs, `ID_Var(`Var_Constant, rvar)) -> update_lhs (StrMap.find rvar map) map lhs
		| MethodCall(lhs_o, { mc_target = Some (`ID_Var(`Var_Local, targ)) }) -> 
				let map = match lhs_o with
					| None -> map
					| Some lhs -> update_lhs MaybeNil map lhs
				in
					map
		| Class(Some lhs, _, _) | Module(Some lhs, _, _)
		| MethodCall(Some lhs, _) | Yield(Some lhs, _)
		| Assign(lhs, _) -> update_lhs MaybeNil map lhs
		| _ -> map
	
	let init_formals args fact =
		List.fold_left
			(fun acc param ->
						update (method_formal_name param) fact acc
			) top args
	
	let empty = StrMap.empty
	
end

module NilDataFlow = Dataflow.Forwards(NilAnalysis)

open Cfg_refactor
open Cfg_printer.CodePrinter

let transform targ node =
	freparse ~env: node.lexical_locals "unless %a.nil? then %a end"
		format_expr targ format_stmt node

class safeNil inf = object(self)
	inherit default_visitor as super
	val facts = inf
	
	method visit_stmt node = (*print_string "VISIT_STMT: ";print_stmt stdout node;*)
		match node.snode with
		| Method(mname, args, body) ->
				let in', out' = NilDataFlow.fixpoint body in
				let me = {< facts = in'>} in
				let body' = visit_stmt (me:> cfg_visitor) body in
				ChangeTo (update_stmt node (Method(mname, args, body')))
		| MethodCall(_, { mc_target = Some (`ID_Var(`Var_Local, var) as targ) }) -> 
				begin try let map = Hashtbl.find facts node in
					begin try match StrMap.find var map with
						| NilAnalysis.MaybeNil -> ChangeTo (transform targ node)
						| NilAnalysis.NonNil -> SkipChildren
					with Not_found -> ChangeTo (transform targ node)
					end
				with Not_found -> print_string "ASSERTFALSE\n";print_stmt stdout node;assert false
				end
		| MethodCall(_, { mc_target = Some (`ID_Var(`Var_Constant, var) as targ) }) -> 
				begin try let map = Hashtbl.find facts node in
					begin try match StrMap.find var map with
						| NilAnalysis.MaybeNil -> ChangeTo (transform targ node)
						| NilAnalysis.NonNil -> SkipChildren
					with Not_found -> ChangeTo (transform targ node)
					end
				with Not_found -> assert false
				end
		| MethodCall(_, { mc_target = Some (#expr) }) 
		| MethodCall(_, _) -> SkipChildren
		| _ -> super#visit_stmt node
end
(* open Dynamic module NilProfile : DynamicAnalysis = struct module Domain *)
(* = Yaml.YString module CoDomain = Yaml.YBool let name = "dynnil" let     *)
(* really_nonnil lookup mname pos = let uses = lookup mname pos in if uses *)
(* = [] then false else not (List.mem false uses) class dyn_visitor lookup *)
(* ifacts = object(self) inherit (safeNil ifacts) as super method          *)
(* visit_stmt node = match node.snode with | Method(defname,args,body) ->  *)
(* let mname = format_to_string format_def_name defname in let init_facts  *)
(* = if really_nonnil lookup mname body.pos then NilAnalysis.init_formals  *)
(* args NilAnalysis.NonNil else NilAnalysis.top in let in',_ =             *)
(* NilDataFlow.fixpoint body in let me = {<facts = in'>} in let body' =    *)
(* visit_stmt (me:>cfg_visitor) body in ChangeTo (update_stmt node         *)
(* (Method(defname,args,body'))) | _ -> super#visit_stmt node end let      *)
(* transform_cfg lookup stmt = compute_cfg stmt; compute_cfg_locals stmt;  *)
(* let i,_ = NilDataFlow.fixpoint stmt in visit_stmt (new dyn_visitor      *)
(* lookup i :> cfg_visitor) stmt let instrument_ast ast = ast let get_pos  *)
(* pos = pos.Lexing.pos_fname, pos.Lexing.pos_lnum let format_param ppf p  *)
(* = Format.pp_print_string ppf (method_formal_name p) open Cfg.Abbr let   *)
(* instrument mname args body pos = let file, line = get_pos pos in let    *)
(* code = freparse ~env:body.lexical_locals                                *)
(* "DRuby::Profile::Dynnil.watch('%s',%d,self,'%a',[%a])" file line        *)
(* format_def_name mname (format_comma_list format_param) args in let      *)
(* body' = seq [code;body] body.pos in meth mname args body' pos let       *)
(* should_instrument stmt = true class instrument_visitor = object(self)   *)
(* inherit default_visitor as super method visit_stmt stmt = match         *)
(* stmt.snode with | Method(mname,args,body) -> if should_instrument stmt  *)
(* then ChangeTo (instrument mname args body stmt.pos) else SkipChildren | *)
(* _ -> super#visit_stmt stmt end let instrument_cfg stmt = compute_cfg    *)
(* stmt; compute_cfg_locals stmt; visit_stmt (new instrument_visitor) stmt *)
(* let transform_ast ym ast = ast end let dyn_main fname = let module Dyn  *)
(* = Make(Singleton(NilProfile)) in let loader = File_loader.create        *)
(* File_loader.EmptyCfg ["../lib"] in print_stmt stdout (Dyn.run loader    *)
(* fname)       *)
(* *)

let print_hash ifs = 
            Hashtbl.iter (fun k v -> 
                (*print_string "Statement: \n";*)
                print_string "\n";
                print_stmt stdout k;
                print_string(" ->  ");
                    if ((StrMap.is_empty v) == false) then
                        StrMap.iter (
                                fun k w -> 
                                        print_string "(";
                                        print_string k;
                                        print_string ", ";
                                        match w with
																					| NilAnalysis.MaybeNil -> print_string "MaybeNil\n"
																					| NilAnalysis.NonNil -> print_string "NonNil\n"
                        ) v 
                    else
                        print_string "\n";
            ) ifs
						;;


let main fname =
	let loader = File_loader.create File_loader.EmptyCfg [] in
	let s = File_loader.load_file loader fname in
	Printf.printf("##### BEGIN INPUT ####\n"); print_stmt stdout s; Printf.printf("##### END INPUT #####\n");
	let () = compute_cfg s in
	Printf.printf("##### BEGIN CFG ####\n"); print_stmt stdout s; Printf.printf("##### END CFG #####\n");
	let () = compute_cfg_locals s in
	Printf.printf("##### BEGIN CFGL ####\n"); print_stmt stdout s; Printf.printf("##### END CFGL #####\n");
	let ifacts, ofacts = NilDataFlow.fixpoint s in
	print_string "@@@@@@@@@@@@@ FINE PRIMO FIXPOINT, INIZIO SAFENIL @@@@@@@@@@@@@\n";
	print_hash ifacts;
	print_string "@@@@@@@@@@@@@ FINE PRIMO FIXPOINT, INIZIO SAFENIL @@@@@@@@@@@@@\n";
	let s' = visit_stmt (new safeNil ifacts :> cfg_visitor) s in
	Printf.printf("##### BEGIN OUTPUT ####\n"); print_stmt stdout s'; Printf.printf("##### END OUTPUT #####\n")

let _ =
	if (Array.length Sys.argv) != 2
	then begin
		Printf.eprintf "Usage: print_cfg <ruby_file> \n";
		exit 1
	end;
	let fname = Sys.argv.(1) in
	(* dyn_main fname; *)
	main fname;
	()
