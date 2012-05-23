open Cfg
open Cfg_printer
open Visitor
open Utils
open Cfg_refactor
open Cfg_printer .CodePrinter
open Printf

module NilAnalysis = struct
	type fact = MaybeNil | NonNil

	let meet_fact t1 t2 = match t1,t2 with
		| MaybeNil, _
		| _, MaybeNil -> MaybeNil
		| NonNil, NonNil -> NonNil

	let update s v map =
		let fact =
			try meet_fact (StrMap.find s map) v
			with Not_found -> v
		in StrMap.add s fact map

	let join lst =
		List.fold_left (fun acc map ->
			StrMap.fold update map acc) StrMap.empty lst

	let fact_to_s = function MaybeNil -> "MaybeNil" | NonNil -> "NonNil"

	type t = fact StrMap.t
	let empty = StrMap.empty
	let eq t1 t2 = StrMap.compare Pervasives.compare t1 t2 = 0 
	let to_string t = strmap_to_string fact_to_s t
	
	let rec update_lhs fact map lhs = match lhs with
		| `ID_Var(`Var_Local, var) -> update var fact map
		| #identifier -> map
		| `Tuple lst -> List.fold_left (update_lhs MaybeNil) map lst
		| `Star (#lhs as l) -> update_lhs NonNil map l

	let transfer map stmt = match stmt.snode with
		| Assign( lhs , #literal ) -> update_lhs NonNil map lhs
		| Assign(lhs, `ID_Var(`Var_Local,rvar)) -> update_lhs (StrMap.find rvar map) map lhs
		| Class(Some lhs, _ , _ ) | Module(Some lhs, _ , _ )
		| MethodCall(Some lhs, _ ) | Yield(Some lhs, _ )
		| Assign( lhs , _ ) -> update_lhs MaybeNil map lhs
		| _ -> map
		
end

module DataNil = Dataflow.Forwards(NilAnalysis)

let refactor targ node =
	let nodee = freparse ~env:node.lexical_locals
		"unless %a.nil? then %a end" format_expr targ format_stmt node
	in ChangeTo nodee

class safeNil ( ifs , ofs ) = object
	inherit default_visitor as super

	method visit_stmt node = match node.snode with
		| Method(mname,args,body) -> SkipChildren 
		| MethodCall( _ , {mc_target=(Some `ID_Self| None)}) -> SkipChildren 
		| MethodCall( _ ,
			{mc_target=Some (`ID_Var(`Var_Local,var) as targ)}) ->
			let map = 
			Hashtbl.find ifs node in 
				begin try match StrMap.find var map with
					| NilAnalysis.MaybeNil -> refactor targ node
					| NilAnalysis.NonNil -> SkipChildren
				with Not_found -> print_string("errore");SkipChildren
				end
		| MethodCall( _ ,{mc_target=Some (#expr as targ)}) -> refactor targ node
		| If( _ , _ , _ ) -> print_string "BECCATO L'IF";SkipChildren
		| _ -> super#visit_stmt node
end

let print_hash (ifs,ofs) = 
	(*let num1 = Hashtbl.length ifs in
	let num2 = Hashtbl.length ofs in
		print_int(num1);print_string(" - ");print_int(num2)*)
	Hashtbl.iter (fun k v -> 
		print_stmt stdout k;print_string("\b    -->   ");
			StrMap.iter (
				fun k v -> 
					print_string k;
					print_string " ###> ";
					match v with
					| NilAnalysis.MaybeNil -> print_string "MaybeNil\n"
					| NilAnalysis.NonNil -> print_string "NonNil\n"
					) v 
			) ifs
	;;

let main fname =
	let loader = File_loader.create File_loader.EmptyCfg [] in
	let s = File_loader.load_file loader fname in
	let () = compute_cfg s in
	let () = compute_cfg_locals s in
	let df = DataNil.fixpoint s in
		print_hash df;printf ("\nfineeeeeee\n");
	let sn = new safeNil df in
	let ss = visit_stmt sn s in
		printf ("\nfine\n");print_stmt stdout ss
		
let _ = 
  if (Array.length Sys.argv) != 2 
  then begin
    Printf.eprintf "Usage: print_cfg <ruby_file> \n";
    exit 1
  end;
  let fname = Sys.argv.(1) in
    (*dyn_main fname;*)
    main fname;
    ()
