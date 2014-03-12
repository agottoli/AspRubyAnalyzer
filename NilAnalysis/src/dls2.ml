open Cfg
open Cfg_printer
open Visitor
open Utils
open Cfg_refactor
open Cfg_printer.CodePrinter
open Printf
open Str
  
(* INIZIO CONTRACT LIVENESS *)
module C = Cfg.Abbr

module LivenessAnalysis = struct

  type fact = Live | Dead
    
  let fact_to_s = function Live -> "Live" | Dead -> "Dead"
    
  let top = StrMap.empty
  type t = fact StrMap.t
  let empty = StrMap.empty
  let eq t1 t2 = StrMap.compare Pervasives.compare t1 t2 = 0 
  let to_string t = strmap_to_string fact_to_s t
    
				
  let meet_fact t1 t2 = match t1,t2 with	
    | _, Live ->  (* print_string "confronto \n"; *) Live			
    | _, Dead -> (* print_string "confronto \n"; *) Dead
      
  let meet_fact_IF t1 t2 = match t1,t2 with	
    | _, Live ->  (* print_string "confronto \n"; *) Live			
    | Live, _ -> (* print_string "confronto \n"; *) Live
    | Dead, Dead -> (* print_string "confronto \n"; *) Dead
      
  let update s v map =
    (* if s <> "\n" then *)
    let fact =
      try meet_fact (StrMap.find s map) v
      with Not_found -> v
    in 
    StrMap.add s fact map	
    (* else map *)
       
  let update_IF s v map =
    let fact =
      try meet_fact_IF (StrMap.find s map) v
      with Not_found -> v
    in 
    StrMap.add s fact map	
      
  let join lst =		(*join receives a list of StrMap (String, fact) *) 
    (* print_string "joinnnnnnn \n" ; *)
   	if (List.length lst) > 1 then
      let map1 = (fun acc map -> StrMap.fold update_IF map acc) (List.nth lst 0) (List.nth lst 1) in
      let map2 = (fun acc map -> StrMap.fold update_IF map acc) (List.nth lst 1) (List.nth lst 0) in
      (fun acc map -> StrMap.fold update_IF map acc) map1 map2		(* now map1 and map2 are defined on the same set of variables *)
    else
      List.fold_left (fun acc map ->
        StrMap.fold update map acc) StrMap.empty lst   

  let rec update_lhs fact map lhs = 
    let map = match lhs with
    | `ID_Var(`Var_Local, var) -> update var fact map
    | `ID_Var(`Var_Constant, const) -> update const fact map
    | #identifier -> map
    | `Tuple lst -> List.fold_left (update_lhs fact) map lst
    | `Star (#lhs as l) -> print_string "asdasd\n"; update_lhs fact map l
    in map

  let update_use lhs value map =
    let map = update_lhs Dead map lhs 
    in let map = update value Live map
  in map


  (* VISITE *)

  let rec visit_literal lit fact map =
    print_string "ALE visit_literal:\n";
    match lit with 
      | `Lit_Array star_lst -> print_string "ALE star_list:\n"; 
                              (* qua ci vanno le robe del for tipo [[a,b][c,4]] *)
                              (* let map = List.fold_left (fun acc x -> visit_star_expr x fact acc) map star_lst in map *)
                              visit_star_expr_list star_lst fact map
      | `Lit_Hash pair_lst ->  print_string "ALE pair_list:\n"; 
                              let map = List.fold_left (fun acc (e1, e2) -> 
                                                  let acc = visit_expr e1 fact acc in
                                                  visit_expr e2 fact acc
                                              ) map pair_lst in map
      | `Lit_Range(b, e1, e2) -> print_string "ALE lit_range:\n";
                                  let map = (visit_expr e1 fact map) in
                                  let map = (visit_expr e2 fact map) in
                                  map 
       |  _ -> print_string "ALE altro!!!"; map 

  and visit_id id fact map = 
    print_string "ALE visit_id:\n";
    match id with
      | `ID_Var(`Var_Local, var) -> print_string "ALE var local.\n"; update var fact map
      | `ID_Var(`Var_Constant, const) -> print_string "ALE var constant.\n"; update const fact map
      | `Tuple lst -> print_string "ALE tuple:\n"; List.fold_left (fun acc x -> visit_expr x fact acc) map lst
      | _ ->  print_string "ALE qualcos'altro!!!\n"; map 

  and visit_expr (e: expr) fact map =
    print_string "ALE visit_expr:\n";
    match e with
      | #literal as l -> (visit_literal l fact map)
      | #identifier as id -> (visit_id id fact map)

  and visit_lhs lhs fact map = 
    let map = match lhs with
    (* identifier *)
    | #identifier as id -> (visit_id id fact map)
    (* lhs tuple *)
    | `Tuple lhs_lst -> List.fold_left (update_lhs fact) map lhs_lst
    (* identifier star *)
    | `Star (#identifier as id) -> visit_id id fact map
    in map

  and visit_lhs_option lhs_o fact map =
    match lhs_o with
     | None -> map
     | Some lhs -> visit_lhs lhs fact map;

  and visit_expr_option expr_o fact map =
    match expr_o with 
      | None -> map
      | Some (`ID_Var(_,_) as var) -> visit_id var fact map
      | _ -> map


  and visit_star_expr star fact map = 
    print_string "ALE visit_star_expr:\n";
    match star with
      | #expr as e -> visit_expr e fact map
      | `Star e -> let map = (visit_expr e fact map) in map


  and visit_tuple_expr tup fact map =
    match tup with 
      | #expr as e -> (visit_expr e fact map)
      | `Star (#expr as e) -> (visit_expr e fact map)
      | `Tuple lst (* -> List.fold_left (fun acc x -> visit_tuple_expr x fact acc) map lst *)
      | `Star (`Tuple lst) -> List.fold_left (fun acc x -> visit_tuple_expr x fact acc) map lst

  and visit_tuple_expr_option tup_o fact map =
    match tup_o with
      | None -> map
      | Some el -> visit_tuple_expr el fact map

  and visit_star_expr_list list fact map = 
    match list with
      | [] -> print_string "lista vuota\n"; map
      | head :: tail -> print_string "lista non vuota\n"; 
                        let map = visit_star_expr_list tail fact map in
                        let map = visit_star_expr head fact map in 
                        map

  let rec visit_method_param p fact map =
    match p with
        | `Formal_block_id(_,s) -> update s fact map
        | `Formal_star(s) -> update s fact map
        | `Formal_tuple(m) -> List.fold_left (fun acc x -> (visit_method_param x fact acc)) map m




  (* TRANSFER *)

  let rec transfer map stmt = match stmt.snode with
  
    | Assign(lhs , #literal) | Assign(lhs , `ID_True) | Assign(lhs , `ID_False) -> print_string "ALE assign true, false o literal\n"; 
                                                                                    visit_lhs lhs Dead map
    | Assign(lhs , `ID_Nil) -> print_string "ALE assign null\n" ;
                                visit_lhs lhs Dead map 
 (*   | Assign(lhs, (`ID_Var(`Var_Local, rvar) as var)) ->  print_string "var\n";
                                                  let map = visit_lhs lhs Dead map in let map = visit_id var Live map in map (* update_use lhs rvar map *)
    | Assign(lhs, `ID_Var(`Var_Constant, rconst)) ->  print_string "constant\n"; update_use lhs rconst map *)
    | Assign(lhs, (`ID_Var(_, _) as var)) -> print_string "ALE assign id_var\n" ;
                let map = visit_lhs lhs Dead map in 
                visit_expr var Live map

    | Assign(lhs, (`Tuple(_) as tup)) -> print_string "ALE assign tuple\n" ; 
                let map = visit_lhs lhs Dead map in
                visit_tuple_expr tup Live map 
                                            

                      (* {mc_target = Some (`ID_Var(_,_) as target); mc_args = args} *)
    | MethodCall(lhs_o, {mc_target = target; mc_args = args} ) -> print_string "MethodCall id_var\n";
                let map = List.fold_left (fun acc x -> visit_star_expr x Live acc) map args in
                let map = visit_lhs_option lhs_o Dead map
                in let map =  visit_star_expr_list args Live map
                in let map = visit_expr_option target Live map
          		  in map

    
    | While((`ID_Var(_, _) as var) , _) -> print_string "while\n";
        visit_expr var Live map


    | For(p, e, _) -> print_string "for preso param\n";      
        let map = List.fold_left(fun acc x -> visit_method_param x Dead acc) map p in 
        let map = visit_expr e Live map in 
        map
    
    | If((`ID_Var(_, _) as var) ,_,_) -> print_string "if\n"; 
        visit_expr var Live map 
    

    | Case(all) -> print_string "case\n"; print_string ("vediamo-> "^(to_string map)); print_string "\n";

          let whens = all.case_whens in
        (* st will contain all the stmt in all the when's clauses *)
          let cond_list = List.fold_left ( fun acc (s, _) -> s::acc) [] whens in
          let map = List.fold_left (fun acc x -> visit_tuple_expr x Live acc) map cond_list in

          let map = visit_expr all.case_guard Live map in map

    | Yield(lhs_o ,args) -> print_string "yield\n";
      let map =  visit_star_expr_list args Live map in
      let map = visit_lhs_option lhs_o Dead map
      in map

   | Return(s)-> print_string "return\n";
        visit_tuple_expr_option s Live map

    | Expression(e) -> print_string "expression\n"; 
        visit_expr e Live map



    (*    ELIMINABILI 

    | Module(_,_,_)-> print_string "module\n"; map

    | Expression(_) -> print_string "expression\n"; map

    | Alias(_) -> print_string "alias\n"; map

    | Class(_,_,_)-> print_string "class\n"; map

    | Seq(_) -> print_string "seq\n"; map

    | Begin(_) -> print_string "begin\n"; map

    | End(_)-> print_string "end\n"; map 

    | ExnBlock(_)-> print_string "exnblock\n"; map

    | Method (_,_,_)-> print_string "method def\n"; map

    | Break(_) -> print_string "break niente \n"; map

*)
    (*| Break(`ID_Var(`Var_Local, rvar)) -> print_string "break\n"; update rvar Live map
    | Break(`ID_Var(`Var_Constant, rvar)) -> print_string "break\n"; update rvar Live map
*)

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

    (* INIZIOOOOOOOOOOOOOOOOOOOOOOOOOOOOOO *)
let justif input =
  let lines = split (regexp_string "\n") input in
  let fields_l = List.map (split (regexp_string "$")) lines in
  let fields_l = List.map Array.of_list fields_l in
  let n = (* number of columns *)
    List.fold_left
      (fun n fields -> max n (Array.length fields))
      0 fields_l
  in
  let pads = Array.make n 0 in
  List.iter (
    (* calculate the max padding for each column *)
    Array.iteri
      (fun i word -> pads.(i) <- max pads.(i) (String.length word))
  ) fields_l;

  let print f =
    List.iter (fun fields ->
      Array.iteri (fun i word ->
        f word (pads.(i) - (String.length word))
      ) fields;
      print_newline()
    ) fields_l;
  in

  (* left column-aligned output *)
  print (fun word pad ->
    let spaces = String.make pad ' ' in
    Printf.printf "%s%s " word spaces)

    (* FINEEEEEEEEEEEEEEEEEEEEEEEE *)

		let print_pos node pos =
    print_string "[WARNING]: Dead var: \n in method call "; print_stmt stdout node; 
    Printf.printf " at %s:%d \n"
      pos.Lexing.pos_fname pos.Lexing.pos_lnum; 
    flush_all () 
  (* Printf.printf "[WARNING]: MaybeNil dereference in %s at line %d \n" *)
  (* pos.Lexing.pos_fname pos.Lexing.pos_lnum; *)
  (* flush_all () *)


    let rec get_for_strings l =
    List.fold_left ( fun acc el ->
      match el with
        | `Formal_block_id(_,s) -> s :: acc
        | `Formal_star(s) -> s :: acc
        | `Formal_tuple(m) -> get_for_strings m
    ) [] l

    let rec get_indent_string level = 
          match level with
            | 0 -> ""
            | _ -> "   "^(get_indent_string (level-1))


  let print_row_table k map level =
    (* print_int stdout k; *)
     let cell = ref "" in
     cell:= !cell^(get_indent_string level)^(string_of_cfg k);
     cell:=!cell^"$|$";
     match (StrMap.is_empty map) with
      | true -> cell:= !cell^"$|\n"; !cell
      | false -> StrMap.iter (
                     fun k w -> 
                      cell:= !cell^"("^k^", ";
                      match w with
                        | LivenessAnalysis.Dead -> cell := !cell^"Dead) "
                        | LivenessAnalysis.Live -> cell := !cell^"Live) "
                    ) map; cell := !cell^"$|\n";
      !cell

  let print_row_nostmt map =
    (* print_int stdout k; *)
     match (StrMap.is_empty map) with
      | true -> "$|\n"
      | false -> let cell = ref "" in 
                    StrMap.iter (
                     fun k w -> 
                      cell:= !cell^"("^k^", ";
                      match w with
                        | LivenessAnalysis.Dead -> cell := !cell^"Dead) "
                        | LivenessAnalysis.Live -> cell := !cell^"Live) "
                    ) map; !cell^"$|\n"


      


    let rec print_var_table stmt out_tbl level =
      match stmt.snode with
      | Seq(list) ->
          let cell = ref "" in
          List.iter( fun x -> 
                      cell:= !cell^(print_var_table x out_tbl level)) list;
          !cell
      | While(g, b) ->
          let cell = ref "" in
          cell:= !cell^"("^(string_of_int(stmt.pos.Lexing.pos_lnum))^")$|$"^(get_indent_string level)^"while "^(string_of_expr g)^"$|$";
          cell:= !cell^(print_row_nostmt (Hashtbl.find out_tbl stmt));
          cell:= !cell^(print_var_table b out_tbl (level+1));
          cell:= !cell^"("^(string_of_int(stmt.pos.Lexing.pos_lnum))^")$|$"^(get_indent_string level)^"end$|$$|\n";
          !cell

      | If(g, t, f) ->

        let cell = ref "" in
        cell:= !cell^"("^(string_of_int(stmt.pos.Lexing.pos_lnum))^")$|$"^(get_indent_string level)^"if "^(string_of_expr g)^" then $|$";
        cell:= !cell^(print_row_nostmt (Hashtbl.find out_tbl stmt));
        cell:= !cell^(print_var_table t out_tbl (level+1));
        cell:= !cell^"("^(string_of_int(stmt.pos.Lexing.pos_lnum))^")$|$"^(get_indent_string level)^"else$|$$|\n";
        cell:= !cell^(print_var_table f out_tbl (level+1));
        cell:= !cell^"("^(string_of_int(stmt.pos.Lexing.pos_lnum))^")$|$"^(get_indent_string level)^"end$|$$|\n";
        !cell

      | For(p,g,b) ->
        let cell = ref "" in
        cell:= !cell^"("^(string_of_int(stmt.pos.Lexing.pos_lnum))^")$|$"^(get_indent_string level)^"for "^(String.concat " " (get_for_strings p))^" in "^(string_of_expr g)^" do$|$";
        cell:= !cell^(print_row_nostmt (Hashtbl.find out_tbl stmt));
        cell:= !cell^(print_var_table b out_tbl (level+1));
        cell:= !cell^"("^(string_of_int(stmt.pos.Lexing.pos_lnum))^")$|$"^(get_indent_string level)^"end$|$$|\n";
        !cell

      | Case (b) ->
        let cell = ref "" in
        cell:= !cell^"("^(string_of_int(stmt.pos.Lexing.pos_lnum))^")$|$"^(get_indent_string level)^"case "^(string_of_expr b.case_guard)^"$|$";
        cell:= !cell^(print_row_nostmt (Hashtbl.find out_tbl stmt));
        let whens = b.case_whens in
        (* st will contain all the stmt in all the when's clauses *)
        List.iter(fun (e,s) -> 
                  (* cell := (fun num ->
                      match num with
                        | 0 -> !cell^""
                        | _ -> !cell^"  "^ ) 1; *)

                  cell:= !cell^"("^(string_of_int(stmt.pos.Lexing.pos_lnum))^")$|$"^(get_indent_string level)^"when "^(string_of_tuple_expr e)^" then$|$";
                  (* se si vuole la tabella anche del when usare la riga sotto *)
                  let m_new = (Hashtbl.find out_tbl s) in 
                  let m_new = (StrMap.add (string_of_tuple_expr e) LivenessAnalysis.Live m_new) in
                  cell := !cell^(print_row_nostmt m_new);
                  (* altrimenti usare quest'altra *)
                  (* cell := !cell^"$|\n"; *)
                  
                  (* ricorsiva per gli statement dentro al when *)
									cell := !cell^(print_var_table s out_tbl (level+1));
        ) whens;

        cell:= (fun x -> match x with
                | None -> !cell
                | Some s -> 
									cell := !cell^"("^(string_of_int(stmt.pos.Lexing.pos_lnum))^")$|$"^(get_indent_string level)^"else$|$"; 
                  (* se si vuole la tabella anche del'else usare la riga sotto *)
                  cell := !cell^(print_row_nostmt (Hashtbl.find out_tbl s));
                  (* altrimenti usare quest'altra *)
                  (* cell := !cell^"$|\n"; *)

                  (* ricorsiva per gli statement dentro all'else *)
									!cell^(print_var_table s out_tbl (level+1))
									) b.case_else; 

        cell:= !cell^"("^(string_of_int(stmt.pos.Lexing.pos_lnum))^")$|$"^(get_indent_string level)^"end$|$$|\n";
        !cell

      | _ ->  let cell = ref "" in
          cell:= !cell^"("^(string_of_int(stmt.pos.Lexing.pos_lnum))^")$|$"^(print_row_table stmt (Hashtbl.find out_tbl stmt) (level));
          !cell
                
(* print_string "("; Printf.printf "%d) \t" stmt.pos.Lexing.pos_lnum;
              print_row_table stmt (Hashtbl.find out_tbl stmt) *)

      (* let list_tbl = 
        Hashtbl.fold (fun k v acc -> k :: acc) out_tbl [] in

        let sorted = List.sort (fun x y -> Pervasives.compare x.pos y.pos ) list_tbl in
        List.iter (fun x -> match x.snode with
                            | Seq(_) -> print_string ""
                            | _ -> print_row_table x (Hashtbl.find out_tbl x)
        ) sorted *)

      
  let refactor targ node =
    let nodee = freparse ~env:node.lexical_locals
      "unless %a.nil? then %a end" format_expr targ format_stmt node
    in ChangeTo nodee
      
  let print_warning node =
    print_pos node node.pos;
  (* print_stmt stdout node *)


    (* ELIMINARE *)
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

(* PARTI DA QUI *)
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
  print_string "--------------------------------------------\n\n";  
  print_string "Live In Variables Table: \n \n";
  justif (print_var_table s ifs 0);
  print_string "--------------------------------------------\n\n";  
  print_string "Live Out Variables Table: \n \n";
  justif (print_var_table s ofs 0);

  (* let sn = ( new analizeLivenes ifs :> cfg_visitor ) in
  let _ = visit_stmt (sn) s in *)
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

