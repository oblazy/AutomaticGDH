(*R�cup�re un fichier texte avec des lignes de la forme M1 - R1 > M2, et le transforme en lpi exploitable par le graph*)
(*Et pr�pare l'algorithme d'attaque *)

let rec suppr_esp s =
if String.contains s ' ' then
let i = String.index s ' ' in
(String.sub s 0 i)^(suppr_esp ((String.sub s (i+1) (String.length s -i-1))))
else s;;

let rec suppr_pt s =
if String.contains s '.' then
let i = String.index s '.' in
(String.sub s 0 i)^(suppr_pt ((String.sub s (i+1) (String.length s -i-1))))
else s;;

let rec saufc s = (*enl�ve les commentaires en fin de ligne *)
if String.contains s '%' then
let i = String.index s '%' in
(String.sub s 0 i)
else s;;

let rec parent s =
if String.contains s '(' then
let i = String.index s '(' and j= String.index s ')' in
(String.sub s 0 i,String.sub s (i+1) (j-i-1))
else (s,"");;

let prot_of_string s =
let t= suppr_esp s in
let i = String.index t '-' and j =  String.index t '>' in
let (a,o) = parent(String.sub t 0 i) and b = String.sub t (i+1) (j-i-1) and c = (String.sub t (j+1) (String.length t -j-1)) in 
(int_of_string(a),b^"-"^o,int_of_string(c));;

let rec epureprot b a c o=
match b with
"" -> []
|s -> if String.contains s ',' then
let i = String.index s ',' in
(a,(String.sub s 3 (i-4))^"-"^o,c)::(epureprot (String.sub s (i+1) (String.length s - i-1)) a c o)
else [(a,(String.sub s 3 (String.length s - 4))^"-"^o,c)];;

let prot2_of_string s =
let t= suppr_esp (suppr_pt s) in
let i = String.index t '-' and j =  String.index t ':' in
let (a,o) = parent(String.sub t 0 i) and b = (String.sub t (j+1) (String.length t - j-1)) and c = (String.sub t (i+3) (j-i-3)) in 
epureprot b (int_of_string a) (int_of_string c) o;;

type 'a transmit = R of 'a * int
               |K of 'a * 'a
               |Mm;;

type 'a comm = 'a transmit list;;

let lire nom =
 let c = open_in nom in
 let rec lire_prot c =
 let prot=ref[] in
 let rec aux () =
  try match  (input_line c) with
	|""-> aux ()
	|"==EOF==" -> ()
	|s when s.[0]='%' -> aux ()
	|s when s.[0]='M' -> (prot:= ((prot2_of_string (saufc s) ) @ !prot) ; aux () )
	|s -> (prot:= ((prot_of_string (saufc s) ) :: !prot) ; aux () )
	with End_of_file -> ()
  in aux ();
 !prot
 in
 let prot =ref (lire_prot c) in
close_in c;
!prot;;


let rec miroir l ll=
match l with
[] -> ll
|p::q -> miroir q (p::ll);;

let rec f1 a l ll=
match l with
[] -> (1,(a,1)::(l@ll))
|(p,q)::t -> if p = a then (q+1, (a,q+1)::(t@ll)) else f1 a t ((p,q)::ll);;

let f2 a (j,l)=
let (i,ll)=f1 a l []in
(i,j,ll);;

let rec find a c l=
f2 a (f1 c l []);;

let rec ctransmi l li=
match l with
[] -> []
| (a,b,c)::q -> 
let (i,j,nl)=find a c li in
((a,i),b,(c,j)):: (ctransmi q nl);;


let chiffre a=
let s=String.make 1 a in
("1"=s || "2"=s || "3"=s || "4"=s || "5"=s || "6"=s || "7"=s || "8"=s || "9"=s || "0"=s);;

let cherche s=
let i =ref 0 in begin
while !i < (String.length s -2) && chiffre (s.[!i+1]) do 
incr i;
done;
(String.sub s 0 (!i+1),String.sub s (!i+1) (String.length s - !i-1));end;;

let cherche2 s=
let (a,b)=cherche s in
let (c,d)= cherche (String.sub b 1 (String.length b -1)) in (a,c,d);;

let decoupe s=
let i =ref 0 in begin
while !i < (String.length s -1) && chiffre (s.[!i+1]) do 
incr i;
done;
if !i = String.length s -1 then (int_of_string(s),"") else (int_of_string(String.sub s 0 (!i+1)),String.sub s (!i+1) (String.length s - !i-1));end;;

let cherch s =
	let (a,b)=decoupe s in begin
		if b = "" || b.[0] = 'K' || b.[0] = 'R' || b.[0] = '-' then (a,1,b) else
		if String.length b=1 then failwith ("aie") else
		let (c,d)=decoupe (String.sub b 1 (String.length b -1)) in
		(a,c,d); end;;
(* let i=ref (String.length s-1) and seul=ref true in *)

let rec st2tr s=
	match s with
		"" -> []
		|s when s.[0] = 'K' ->let (a,b,c) = cherche2 (String.sub s 1 (String.length s -1)) in K(int_of_string(a),int_of_string(b))::(st2tr c)
		|s when s.[0] = 'R' ->let (a,b,c) = cherch (String.sub s 1 (String.length s -1)) in R(a,b)::(st2tr c)
		|s when s.[0] = '-' -> []
		|_ -> failwith ("Syntaxe non reconnue (lect)"^s);;  

let rec nettoie l c=
match l with
[] -> []
|K(a,b)::q -> if a=c ||b=c then nettoie q c else K(a,b)::(nettoie q c)
|R(a,b)::q -> if a=c then nettoie q c else R(a,b)::(nettoie q c)
|Mm::q -> Mm::(nettoie q c);;

let eg a b=
match a with
R(c,d) -> begin match b with R(e,f) -> c=e && d=f
		|_ -> false;end
|K(c,d) -> begin match b with K(e,f) -> (c=e && d=f)||(c=f && d=e)
		|_ -> false;end
|Mm -> begin match b with Mm -> true
		|_ -> false;end;;

let rec app a l=
match l with
[] -> false
|p::q -> if eg p a then true else app a q;;

let rec dans l1 l=
match l1 with
[] -> true
|p::q -> if app p l then dans q l else false;;

let sous_mot a b c= (* a sous mot de b ?*)
let aa=nettoie (st2tr a) c and bb=nettoie (st2tr b) c in
dans aa bb;;

let ancetre s=
if String.contains s '-' then
let i = String.index s '-' in
if i=(String.length s -1) then ((false,0),String.sub s 0 i)
else ((true,int_of_string(String.sub s (i+1) (String.length s -i-1))),String.sub s 0 i);
else ((false,0),s);;

(* let rec lookpif ((a,aa),b,(c,cc)) p =
match p with
[]-> (false,[])
|a::[] -> failwith ("En th�orie il y a un nombre pair de noeuds")
|(d,e,s)::((f,g,h)::q) -> let ((ob,oo),j)=ancetre h in 
    if ((d=c)&&(ob && cc=oo)) then begin (true,(a,aa,"")::[(c,cc,b)]);end
    else (lookpif ((a,aa),b,(c,cc)) q);;*)

(* true ... si ancetre pr�d�fini, false sinon*)

let rec lookpi ((a,aa),b,(c,cc)) p =
match p with
[]-> (false,[])
|d::[] -> failwith ("En th�orie il y a un nombre pair de noeuds")
|(d,e,s)::((f,g,h)::q) -> if (d=c &&  cc < e) then
let ((ob,oo),j)=ancetre h in 
    if (ob && cc=oo) then (true,(a,aa,"")::((c,cc,b)::p))
    else if ob then let (pib,pil) = (lookpi ((a,aa),b,(c,cc)) q) in (pib,(d,e,s)::((f,g,h)::pil))
		  else if (sous_mot (snd (ancetre b)) j c) then (true,(a,aa,"")::((c,cc,b)::p))
			else let (pib,pil) = (lookpi ((a,aa),b,(c,cc)) q) in (pib,(d,e,s)::((f,g,h)::pil))
else let (pib,pil) = (lookpi ((a,aa),b,(c,cc)) q) in if pib then(pib, pil)
																						else (pib,(d,e,s)::((f,g,h)::pil));; 

let rec traitepi2 (a,b,c) l=
match l with
[] -> []
|p::q ->let (d,e) = (lookpi (a,b,c) p) in
if d then e::q else p ::(traitepi2 (a,b,c) q);;

let rec traitepi (a,b,c) l=
match l with
[] -> [[(fst a,snd a,"");(fst c,snd c,snd(ancetre b))]]
|p::q ->let (d,e) = (lookpi (a,b,c) p) in
if d then e::(traitepi2 (a,b,c) q) else p ::(traitepi (a,b,c) q);;

let rec creepi l ll=
match l with
[] -> ll
|p::q ->creepi q (traitepi p ll);; 

let moinsmoins s=
if String.contains s '-' then
let i = String.index s '-' in
(String.sub s 0 i) else s;;

let rec cleanm l=
match l with
[] -> []
|(a,b,s)::q ->(a,b,moinsmoins s)::(cleanm q);;

let rec cleanml l=
match l with
[] -> []
|p::q -> cleanm(p)::(cleanml(q));;
 
let go file=
cleanml(creepi (miroir(ctransmi(miroir(lire(file)) []) []) []) []);;

(* go "c:/Documents and settings/blazy/My documents/exemple.txt";;*)