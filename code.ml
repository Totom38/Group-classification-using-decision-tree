(** Cette partie du programme NE DOIT EN AUCUN CAS être modifiée sous peine de voir votre code ne pas passer les tests *)

    let usage () =
      Format.fprintf
        Format.err_formatter
        "%s <options>
    
    OPTIONS:
         -h : print this help and exit
         -o <file> : set output to <file>
         --output <file> : set output to <file>
         -ts <int> : set the size of the training set (default : 1000)
         --training-size <int> : set the size of the training set (default : 1000)
         -ds <int> : set the size of the testing data set (default : 10000)
         --training-size <int> : set the size of the testing data set (default : 10000)
         -md <int> : set the max tree depth (default : 10)
         --max-depth <int> : set the max tree depth (default : 10)
    "
      Sys.argv.(0)
         
    let parse_opts () =
      let rec parse l =
        match l with
        | "-h"::l ->
           let _ = usage () in
           exit 0
        | "-o"::output::l' | "--output"::output::l' ->
           ("output",output)::parse l'
        | "-ts"::size::l' | "--training-size"::size::l' ->
           (try
              let _ = int_of_string size in 
             ("training-size", size)::parse l'
           with Failure _ ->
                 let _ = usage () in
                 exit 127
           )     
        | "-ds"::size::l' | "--data-size"::size::l' ->
           (try
              let _ = int_of_string size in 
              ("data-size",size)::parse l'
           with Failure _ ->
                 let _ = usage () in
                 exit 127
           )
        | "-md"::size::l' | "--max-depth"::size::l' ->
           (try
              let _ = int_of_string size in 
              ("max-depth",size)::parse l'
           with Failure _ ->
                 let _ = usage () in
                 exit 127
           )
        | _::_ ->
           let _ = usage () in
           exit 127             
        | [] -> []
      in
      parse (List.tl (Array.to_list Sys.argv))
    
    let raw_opts = parse_opts ()  
          
(* Une position dans le plan est donnée par son abscisse et son ordonnée *)
type pos = { x : float; y : float; };;
    
(* Une couleur est donnée par ses trois composantes *)
type color = {r:int;g:int;b:int};;
    
(* Un ensemble de données sera représenté ici par une liste de couple (pos,color). On pourra supposer qu'une position ne peut pas apparaître deux fois dans cette liste *)
type 'a dataset = (pos*color) list;;
    
let red  = { r = 255; g = 0; b = 0};;
let blue = { r = 0; g = 0; b = 255};;
let white = { r = 255; g = 255; b = 255};;
let black = { r = 0; g = 0; b = 0};;
    
(* fonction de génération pour la courbe de racine carrée. La partie sous la courbe est en [blue], celle au dessus de la courbe est en [red] *)
let generate_sqrt p =
  if p.y*.p.y < p.x then blue else red ;;

(* fonction de génération pour un cercle. La partie dans le cercle  est en [blue], celle à l'extérieur est en [red] *)
let generate_circle p =
  let x = p.x -. 0.5 and y = p.y -. 0.5 in 
  if x*.x +. y*.y < 0.5*.0.5 then blue else red ;;
      
  let generate p =
    if exp (-2.0 *. p.y) *. (abs_float (cos (20.0 *. p.y))) >= p.x ||
      1.0 -. exp (-2.0 *. (1.0 -. p.y)) *. (abs_float (cos (20.0 *. (1.0 -.p.y)))) < p.x then blue else red ;;



(** Début de la partie à implanter *) 
    
open Stdlib

(* type [tree] des predicteur de couleur en fonction du type de donnée d'entrainement. Il vous faut bien sur remplacer le type unit par un type de votre conception *)
type tree =
  | Leaf of color
  | Node of pos * tree * tree * tree * tree ;;
 
(* ( ' a * color ) list -> int -> int -> int * int *)
(* @requires : dataset est un dataset valide, rouge et bleu valent 0 *)
(*@ensures : renvoie le nombre de points rouges et bleus *)
(* @raises : rien *)
let rec compter_couleurs dataset rouge bleu =
  match dataset with
  | [] -> rouge , bleu
  | head::tail -> 
    if (snd head) = red
      then compter_couleurs tail (rouge+1) bleu
    else 
      compter_couleurs tail rouge (bleu+1) ;;
    
(* ( pos * 'a ) list ->
   ( pos * 'a ) list ->
   ( pos * 'a ) list ->
   ( pos * 'a ) list ->
   ( pos * 'a ) list ->
   pos ->
   ( pos * 'a ) list * ( pos * 'a ) list * ( pos * 'a ) list * ( pos * 'a ) list *)
(* @requires : dataset est un dataset valide, les datasets1 ,2 ,3 et 4 sont des listes vides et separations est un couple de flottants *)
(*@ensures : renvoie 4 sous-datasets dans l'ordre NO, NE, SO, SE *)
(* @raises : rien *)
let rec separer_dataset dataset1 dataset2 dataset3 dataset4 data separations =
  match data with
  | [] -> dataset1 , dataset2 , dataset3 , dataset4
  | head::tail -> 
    if (fst head).x < separations.x && (fst head).y >= separations.y
      then separer_dataset (head::dataset1) dataset2 dataset3 dataset4 tail separations
    else if (fst head).x >= separations.x && (fst head).y >= separations.y
      then separer_dataset dataset1 (head::dataset2) dataset3 dataset4 tail separations
    else if (fst head).x < separations.x && (fst head).y < separations.y
      then separer_dataset dataset1 dataset2 (head::dataset3) dataset4 tail separations
    else 
      separer_dataset dataset1 dataset2 dataset3 (head::dataset4) tail separations

(* [build_tree n training] retourne un predicteur de profondeur maximale [n] sur le jeu d'entrainement [training] *)
(* int -> 'a dataset -> tree *)
(* ( ' a * color ) list -> int -> int -> int * int *)
(* @requires : training est un dataset valide, prof est un entier positif *)
(*@ensures : renvoie l'arbre de décision du dataset training *)
(* @raises : rien *)
let build_tree prof training = 
  let rec build_node profondeur dataset separations = 
    let rouge , bleu = compter_couleurs dataset 0 0 in
    if profondeur >= prof + 1 || rouge = 0 || bleu = 0 || rouge + bleu < 2
    then if rouge > bleu then Leaf red else Leaf blue
    else 
      let epsilon = 1.0 /. 2.0 ** (float_of_int profondeur) in
      let dataset1 , dataset2 , dataset3 , dataset4 = separer_dataset [] [] [] [] dataset separations in
      Node (separations,
            build_node (profondeur+1) dataset1 {x=(separations.x -. epsilon); y=(separations.y +. epsilon)},
            build_node (profondeur+1) dataset2 {x=(separations.x +. epsilon); y=(separations.y +. epsilon)},
            build_node (profondeur+1) dataset3 {x=(separations.x -. epsilon); y=(separations.y -. epsilon)},
            build_node (profondeur+1) dataset4 {x=(separations.x +. epsilon); y=(separations.y -. epsilon)}) in
  build_node 0 training {x=0.5; y=0.5} ;; 
    
(* [predict_color tree pos] prédit la couleur du point [pos] à l'aide du prédicteur [tree] *)
(* tree -> pos -> color *)
(* ( ' a * color ) list -> int -> int -> int * int *)
(* @requires : tree est un tree valide, pos est un couple de coordonnées *)
(*@ensures : renvoie la couleur de pos donnée par l'arbre tree *)
(* @raises : rien *)
let rec predict_color tree pos =
  match tree with
  | Leaf color -> color
  | Node (separations,a,b,c,d) -> 
    if pos.x < separations.x && pos.y >= separations.y
    then predict_color a pos
    else if pos.x >= separations.x && pos.y >= separations.y
    then predict_color b pos
    else if pos.x < separations.x && pos.y < separations.y
    then predict_color c pos
    else predict_color d pos ;;
                                        
(* [generate_using_function pos] retourne la couleur du point pos il vous est conseiller de tester vos résultats sur plusieurs generateurs il vous suffit simplement de changer la fonction de génération avant de recompiler/réévaluer le code  *)                                   
let generate_using_function = generate ;;
      
(* let opts = raw_opts *)                            
let opts = ("training-size","1000000")::("output","C:/Users/totom/Desktop/OCAML/test.ppm")::raw_opts 

(* Measure-Command {ocamlc -o test C:\Users\totom\Desktop\OCAML\CODE.ml} *)
(* Measure-Command {ocamlrun test} *)


(* ocamlc -o test C:\Users\totom\Desktop\OCAML\CODE.ml *)
(* ocamlrun test *)

(* fin de la partie à implanter*)
    




(* AUCUNE MODIFICATION NE DOIT ÊTRE FAITE À PARTIR DE CE COMMENATAIRE *)
(* Vous n'avez pas besoin de lire/comprendre cette partie du code *)
    
let generate nb f  =
  let margin = 0.001 in
  List.init nb
    (fun _ ->
      let x = margin +. Random.float (1. -. 2. *. margin) in
      let y = margin +. Random.float (1. -. 2. *. margin) in
      let v = f {x;y} in
      ({x;y}, v)
    )

let ts =
  match List.assoc_opt "training-size" opts with
  | None -> 1000
  | Some s -> int_of_string s

let ds =
  match List.assoc_opt "data-size" opts with
  | None -> 10000
  | Some s -> int_of_string s
                        
let md =
  match List.assoc_opt "max-depth" opts with
  | None -> 10
  | Some s -> int_of_string s
  

let pnm h w tree testing_ds =
  let output = Array.make_matrix h w white in
  (* on commence par la couleur de fond *)
  Array.iteri
    (fun j line ->
      Array.iteri (fun i _ ->
          let x = float_of_int i /. float_of_int w in
          let y = float_of_int j /. float_of_int h in  
          let c = predict_color tree {x;y} in
          output.(h-j-1).(i) <- c
        )
        line
    )
    output;
  (* On imprime le vrai dataset *)
  List.iter
    (fun (pos,color) ->
      let j = h-1-int_of_float (pos.y*.float_of_int h) in
      let i = int_of_float (pos.x*.float_of_int w) in
      let color' = predict_color tree pos in
      output.(j).(i) <- if color=color' then white else black 
    )
    testing_ds;
  output
            
let output_graph h w tree testing_ds =
  match List.assoc_opt "output" opts with
  | None -> ()
  | Some output ->
      try
        let fd = open_out output in
        let fmt = Format.formatter_of_out_channel fd in
        let output = pnm h w tree testing_ds in   
        let _ = Format.fprintf fmt "P3@.%d %d@.255@." h w in
        let _ = Array.iter (Array.iter (fun color -> Format.fprintf fmt "%d %d %d@." color.r color.g color.b)) output in 
        let _ = Format.pp_print_flush fmt () in 
        close_out fd
      with Sys_error s ->
        let _ = Format.fprintf Format.err_formatter "%s@." s in
        exit 127
            
let main () = 
  let training_ds = generate ts generate_using_function in
  let testing_ds = generate ds generate_using_function in
  let tree = build_tree md training_ds in
  let nb_bad_prediction =
    List.fold_left
      (fun nb_bad_prediction (pos,color) -> 
        let color' = predict_color tree pos in
        if color = color'
        then nb_bad_prediction
        else nb_bad_prediction + 1
      )
      0
      testing_ds
  in
let _ =  Format.printf
"training-size = %d
test-size = %d
max-depth = %d
correctness = %03.1f%%@."
ts ds md (100.*.float_of_int (ds-nb_bad_prediction)/.float_of_int ds)
in
output_graph 400 400 tree testing_ds

let _ = main ()