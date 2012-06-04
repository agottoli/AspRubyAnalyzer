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
		(* print_string "UPDATE ";     *)
		(* print_string s;             *)
		(* print_string " -> ";        *)
		(* print_string (fact_to_s v); *)
		(* print_string "\n";          *)
		StrMap.add s fact map
		
	let update2 s v map =
		let fact =
			try meet_fact2 (StrMap.find s map) v
			with Not_found -> MaybeNil
		in 
		(* print_string "UPDATE2 ";    *)
		(* print_string s;             *)
		(* print_string " -> ";        *)
		(* print_string (fact_to_s v); *)
		(* print_string "\n";          *)
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
	
	let empty = StrMap.empty
	
end


let print_hash ifs = 
            Hashtbl.iter (fun k v -> 
                (*print_string "Statement: \n";*)
								print_string (print_snode k);print_string ":\n";
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

let print_map ifs = 
                    StrMap.iter (
                                fun k w -> 
                                        print_string "(";
                                        print_string k;
                                        print_string ", ";
                                        match w with
																					| NilAnalysis.MaybeNil -> print_string "MaybeNil\n"
																					| NilAnalysis.NonNil -> print_string "NonNil\n"
                        ) ifs;;


module NilDataFlow = Dataflow.Forwards(NilAnalysis)

open Cfg_refactor
open Cfg_printer.CodePrinter

let transform targ node =
	freparse ~env: node.lexical_locals "unless %a.nil? then %a end"
		format_expr targ format_stmt node

class safeNil inf = object(self)
	inherit default_visitor as super
	val facts = inf

	method visit_stmt node = (* print_string "VISIT_STMT: ";print_stmt stdout node; *)
		match node.snode with
		| Method(mname, args, body) ->
				let in', out' = NilDataFlow.fixpoint body in
				let me = {< facts = in'>} in
				let body' = visit_stmt (me:> cfg_visitor) body in
				ChangeTo (update_stmt node (Method(mname, args, body')))
		| MethodCall(_, { mc_target = Some (`ID_Var(`Var_Local, var) as targ) }) ->
				begin try let map = Hashtbl.find facts node in
					begin try match StrMap.find var map with
						| NilAnalysis.MaybeNil -> 
							print_string "WARNING: MaybeNil in statement ";
							print_stmt stdout node;
							ChangeTo (transform targ node)
						| NilAnalysis.NonNil -> SkipChildren
					with Not_found -> 
						print_string "WARNING: MaybeNil in statement ";
							print_stmt stdout node;
							ChangeTo (transform targ node)
					end
				with Not_found -> print_string "ASSERTFALSE\n";print_stmt stdout node;assert false
				end
		| MethodCall(_, { mc_target = Some (`ID_Var(`Var_Constant, var) as targ) }) ->
				begin try let map = Hashtbl.find facts node in
					begin try match StrMap.find var map with
						| NilAnalysis.MaybeNil -> 
							print_string "WARNING: MaybeNil in statement ";
							print_stmt stdout node;
							ChangeTo (transform targ node)
						| NilAnalysis.NonNil -> SkipChildren
					with Not_found -> 
						print_string "WARNING: MaybeNil in statement ";
							print_stmt stdout node;
							ChangeTo (transform targ node)
					end
				with Not_found -> assert false
				end
		| MethodCall(_, { mc_target = Some (#expr) })
		| MethodCall(_, _) -> SkipChildren
		| _ -> super#visit_stmt node
end



let main fname =
	let loader = File_loader.create File_loader.EmptyCfg [] in
	let s = File_loader.load_file loader fname in
	Printf.printf("##### BEGIN INPUT ####\n"); print_stmt stdout s; Printf.printf("##### END INPUT #####\n");
	(* let () = compute_cfg s in *)
	(* Printf.printf("##### BEGIN CFG ####\n"); print_stmt stdout s; Printf.printf("##### END CFG #####\n");  *)
	(* let () = compute_cfg_locals s in *) 
	(* Printf.printf("##### BEGIN CFGL ####\n"); print_stmt stdout s; Printf.printf("##### END CFGL #####\n"); *)
	(* Printf.printf("##### BEGIN FIXPOINT ####\n"); *)
	let ifacts,ofacts = NilDataFlow.fixpoint s in
		(* print_string "$$$$$$$$FIXPOINT IFACTS$$$$$$$$\n"; *)
		(* print_hash ifacts; *)
		(* print_string "$$$$$$$$FIXPOINT OFACTS$$$$$$$$\n"; *)
		(* print_hash ofacts; *)
		(* print_string "$$$$$$$$SAFENIL$$$$$$$$\n"; *)
	let _ = visit_stmt (new safeNil ifacts :> cfg_visitor) s in
	Printf.printf("##### END OUTPUT #####\n")

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
