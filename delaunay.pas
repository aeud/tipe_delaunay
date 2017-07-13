program delaunay;

///////////////////////////////////////////////////////////////////////
///////////////////////////////CONSTANTES//////////////////////////////
///////////////////////////////////////////////////////////////////////

const
	(*nombre d'éléments de la liste lors du remplissage aléatoire*)
	NMAX=1000;

///////////////////////////////////////////////////////////////////////
/////////////////////STRUCTURE DE DONNÉES UTILISÉES////////////////////
///////////////////////////////////////////////////////////////////////

type
(*point (x,y)*)
	point=record
		x:real;
		y:real;
		z:real
		end;
(*vecteur (x,y)*)
	vecteur=record
		x:real;
		y:real
		end;
(*droite*)
	droite=record
		p:point;
		v:vecteur
		end;
(*liste double de points*)
	lpt=^lptr;
	lptr=record
		p:point;
		prev:lpt;
		suiv:lpt
		end;
(*liste simple de pointeurs sur la liste double de triangles*)
	llpt=^llptr;
	llptr=record
		l:lpt;
		suiv:llpt
		end;	
(*liste double de triangles*)
	lt=^ltr;
	(*triangle*)
	triangle=record
		p1:lpt;
		p2:lpt;
		p3:lpt;
		t1:lt;
		t2:lt;
		t3:lt;
		h:point
		end;
	ltr=record
		t:triangle;
		prev:lt;
		suiv:lt
		end;
(*liste simple de pointeurs sur la liste double de triangles*)
	llt=^lltr;
	lltr=record
		l:lt;
		suiv:llt
		end;

///////////////////////////////////////////////////////////////////////
////////////////////////////////VARIABLES//////////////////////////////
///////////////////////////////////////////////////////////////////////

var 
	l,l_save:lpt;
	del,del_save:lt;

///////////////////////////////////////////////////////////////////////
///////////////////////PRÉLIMINAIRES DE GÉOMÉTRIE//////////////////////
///////////////////////////////////////////////////////////////////////

procedure creer_point(a,b:real;var p:point);
(*crée le point (a,b)*)
begin
	p.x:=a;
	p.y:=b
end;

procedure point_milieu(a,b:point;var m:point);
(*m est le milieu du segment [a,b]*)
begin
	m.x:=(a.x+b.x)/2;
	m.y:=(a.y+b.y)/2
end;

procedure creer_vecteur(a,b:point;var v:vecteur);
(*crée le vecteur (a,b)*)
begin
	v.x:=b.x-a.x;
	v.y:=b.y-a.y
end;

procedure creer_droite(a,b:point;var d:droite);
(*crée la droite (a,b)*)
var
	v:vecteur;
begin
	creer_vecteur(a,b,v);
	d.p:=a;
	d.v:=v
end;

procedure droite_perp(a,b,p:point;var d:droite);
(*crée la droite perpendiculaire à (a,b) passant pas p*)
var
	v:vecteur;
	aux:real;
begin
	creer_vecteur(a,b,v);
	aux:=v.x;
	v.x:=-v.y;
	v.y:=aux;
	d.p.x:=p.x;
	d.p.y:=p.y;
	d.v.x:=v.x;
	d.v.y:=v.y
end;

procedure droite_mediatrice(a,b:point;var d:droite);
(*crée la droite médiatrice à [a,b]*)
var
	p:point;
begin
	point_milieu(a,b,p);
	droite_perp(a,b,p,d)
end;

function equ_droite(d:droite;var a,b:real):boolean;
(*la droite s'écrit y=a*x+b ou x=a*)
begin
	if d.v.x<>0 then
	begin
		a:=d.v.y/d.v.x;
		b:=d.p.y-a*d.p.x;
		equ_droite:=true;
	end
	else 
	begin
		a:=d.p.x;
		equ_droite:=false
	end
end;

procedure afficher_equ_droite(d:droite);
var
	point1,point2:point;
	n,n2:real;
begin	
	if equ_droite(d,n,n2) then 
	begin
		write('y = ',n,' x + ',n2);writeln;
	end
	else
	begin
		write('x = ',n);writeln
	end
end;
	

procedure point_intersection_droite(d1,d2:droite;var i:point);
(*i est le point d'interséction des droites d1 et d2*)
(*la procédure ne prend pas en compte le cas où les droites seraient parallèles*)
var
	a1,b1,a2,b2:real;
	eq1,eq2:boolean;
begin
	if d1.v.x*d2.v.y<>d2.v.x*d1.v.y then
	begin
		eq1:=equ_droite(d1,a1,b1);
		eq2:=equ_droite(d2,a2,b2);
		if eq1 then
		begin 
			if eq2 then
			begin
				i.x:=(b2-b1)/(a1-a2);
				i.y:=a1*i.x+b1
			end
			else
			begin
				i.x:=a2;
				i.y:=a1*i.x+b1			
			end
		end
		else
		begin
			i.x:=a1;
			i.y:=a2*i.x+b2
		end
	end
end;

function appartient_droite(p,a,b:point):boolean;
begin
	appartient_droite:=(((b.x-p.x)*(a.y-p.y)=(b.y-p.y)*(a.x-p.x)))
end;

function appartient_segment(p,a,b:point):boolean;
begin
	appartient_segment:=((appartient_droite(a,b,p))and(((a.x<=p.x)and(p.x<=b.x))or((a.x>=p.x)and(p.x>=b.x))))
end;

function distance_carree(a,b:point):real;
(*renvoie la distance au carrée entre les points a et b*)
begin
	distance_carree:=(b.x-a.x)*(b.x-a.x)+(b.y-a.y)*(b.y-a.y)
end;

procedure afficher_point(p:point);
begin	
	write('(',p.x,',',p.y,')')
end;

function point_id(p1,p2:point):boolean;
begin
	if (p1.x=p2.x) and (p1.y=p2.y) then point_id:=true else point_id:=false
end;

///////////////////////////////////////////////////////////////////////
//////////////////OPÉRATIONS SUR LES LISTES DE POINTS//////////////////
///////////////////////////////////////////////////////////////////////

function card_lpt(l:lpt):integer;
(*renvoie le cardinal de la liste de points*)
var
	i:integer;
begin
	if l=nil then card_lpt:=0 else
	begin
		i:=1;
		while l^.suiv<>nil do l:=l^.suiv;
		while l^.prev<>nil do
		begin
			i:=i+1;
			l:=l^.prev
		end;
		card_lpt:=i
	end
end;

function appartient_lpt(p,l:lpt):boolean;
var
	test:boolean;
begin
	test:=false;
	while l^.prev<>nil do l:=l^.prev;
	while l<>nil do 
	begin
		if point_id(p^.p,l^.p) then test:=true;
		l:=l^.suiv
	end;
	appartient_lpt:=test
end;

function initialiser_lpt(p:point):lpt;
(*initialisation de la liste de points*)
var
	aux:lpt;
begin
	new(aux);
	aux^.suiv:=nil;
	aux^.prev:=nil;
	aux^.p:=p;
	initialiser_lpt:=aux
end;

function remplir_lpt(p:point;l:lpt):lpt;
(*ajouter un élément à une liste de points*)
var
	aux:lpt;
begin
	new(aux);
	l^.suiv:=aux;
	aux^.prev:=l;
	aux^.p:=p;
	aux^.suiv:=nil;
	remplir_lpt:=aux
end;

function inserer_lpt(p:point;l:lpt;n:integer):lpt;
(*ajoute un élément dans la liste de points en n-ième position*)
var
	aux,aux2:lpt;
	i:integer;
begin
	aux:=l;
	for i:=1 to n do l:=l^.prev;
	new(aux2);
	aux2^.prev:=l^.prev;
	aux2^.suiv:=l;
	l^.prev^.suiv:=aux2;
	l^.prev:=aux2;
	aux2^.p:=p;
	inserer_lpt:=aux
end;

function copier_lpt(l:lpt):lpt;
var
	newlpt:lpt;
begin
	newlpt:=nil;
	while l^.prev<>nil do l:=l^.prev;
	if l<>nil then
	begin
		newlpt:=initialiser_lpt(l^.p);
		l:=l^.suiv
	end;
	while l<>nil do
	begin
		newlpt:=remplir_lpt(l^.p,newlpt);
		l:=l^.suiv
	end;
	copier_lpt:=newlpt
end;

procedure afficher_lpt(l:lpt);
(*affiche la liste de points l*)
begin
	writeln;
	writeln('/////////////////////////////////////////////////////////////////////////');
	writeln('/////////////////////////////LISTE DE POINTS/////////////////////////////');
	writeln('/////////////////////////////////////////////////////////////////////////');
	writeln;
	while l^.prev<>nil do l:=l^.prev;
	while l<>nil do 
	begin
		write('           ');afficher_point(l^.p);writeln;
		l:=l^.suiv
	end;
	writeln;
	writeln('////////////////////////////////////////////////////////////////////////');
	writeln('////////////////////////////////////////////////////////////////////////');
	writeln
end;

(*écrit la liste de points dans un fichier*)
procedure ecrire_lpt(l:lpt);
var
	f:text;
begin
	assign(f,'/mnt/sda4/Documents/Progra/spé2/tipe/files/points');
	rewrite(f);
		writeln(f);
		writeln(f,'/////////////////////////////////////////////////////////////////////////');
		writeln(f,'/////////////////////////////LISTE DE POINTS/////////////////////////////');
		writeln(f,'/////////////////////////////////////////////////////////////////////////');
		writeln(f);
		while l^.prev<>nil do l:=l^.prev;
		while l<>nil do 
		begin
			writeln(f,'            (',l^.p.x,' ,',l^.p.y,' )');
			l:=l^.suiv
		end;
		writeln(f,'                                  ***');
	close(f)
end;

procedure supprimer_lpt(l:lpt);
var
	laux:lpt;
begin
	while l^.prev<>nil do l:=l^.prev;
	while l<>nil do
	begin
		laux:=l^.suiv;
		dispose(l);
		l:=laux
	end;
end;

///////////////////////////////////////////////////////////////////////
////////////////OPÉRATIONS SUR LES LISTES DE TRIANGLES/////////////////
///////////////////////////////////////////////////////////////////////

function card_lt(l:lt):integer;
(*renvoie le cardinal de la liste de triangles*)
var
	i:integer;
begin
	if l=nil then card_lt:=0 else
	begin
		i:=1;
		while l^.suiv<>nil do l:=l^.suiv;
		while l^.prev<>nil do
		begin
			i:=i+1;
			l:=l^.prev
		end;
		card_lt:=i
	end
end;

procedure creer_triangle_first(a,b,c:lpt;var t:triangle);
(*créée un triangle vierge*)
var
	d1,d2:droite;
	p:point;
begin
	t.p1:=a;
	t.p2:=b;
	t.p3:=c;
	t.t1:=nil;
	t.t2:=nil;
	t.t3:=nil;
	
	droite_mediatrice(a^.p,b^.p,d1);
	droite_mediatrice(a^.p,c^.p,d2);
	point_intersection_droite(d1,d2,p);
	
	t.h.x:=p.x;
	t.h.y:=p.y
end;

procedure copie_triangle(t:triangle;var c:triangle);
(*copie le triangle*)
begin
	c.p1:=t.p1;
	c.p2:=t.p2;
	c.p3:=t.p3;
	c.t1:=t.t1;
	c.t2:=t.t2;
	c.t3:=t.t3;
	c.h.x:=t.h.x;
	c.h.y:=t.h.y
end;

function voisin_arrete(l:lt;p1,p2:lpt):lt;
(*renvoie le voisin du triangle l possédant les points p1 et p2 comme sommets*) 
begin
	if ((l^.t.p1=p1) and (l^.t.p2=p2)) or ((l^.t.p2=p1) and (l^.t.p1=p2)) then voisin_arrete:=l^.t.t3
	else if ((l^.t.p2=p1) and (l^.t.p3=p2)) or ((l^.t.p3=p1) and (l^.t.p2=p2)) then voisin_arrete:=l^.t.t1
	else if ((l^.t.p3=p1) and (l^.t.p1=p2)) or ((l^.t.p1=p1) and (l^.t.p3=p2)) then voisin_arrete:=l^.t.t2
	else writeln('error voisin_arrete')
end;

function voisin_arrete_2(l:lt;p1,p2:point):lt;
(*renvoie le voisin du triangle l possédant les points p1 et p2 comme sommets*) 
begin
	if ((point_id(l^.t.p1^.p,p1)) and (point_id(l^.t.p2^.p,p2))) or ((point_id(l^.t.p1^.p,p2)) and (point_id(l^.t.p2^.p,p1))) then voisin_arrete_2:=l^.t.t3
	else if ((point_id(l^.t.p2^.p,p1)) and (point_id(l^.t.p3^.p,p2))) or ((point_id(l^.t.p2^.p,p2)) and (point_id(l^.t.p3^.p,p1))) then voisin_arrete_2:=l^.t.t1
	else if ((point_id(l^.t.p3^.p,p1)) and (point_id(l^.t.p1^.p,p2))) or ((point_id(l^.t.p3^.p,p2)) and (point_id(l^.t.p1^.p,p1))) then voisin_arrete_2:=l^.t.t2
	else writeln('error voisin_arrete_2')
end;

function voisin_de_voisin(l,v:lt):integer;
(*renvoie le numéro i de triangle tel que v^.t.t[i]=l^.t*) 
begin
	if v^.t.t1=l then voisin_de_voisin:=1
	else if v^.t.t2=l then voisin_de_voisin:=2
	else if v^.t.t3=l then voisin_de_voisin:=3
	else voisin_de_voisin:=0
end;

function troisieme_point(t:lt;p1,p2:lpt):lpt;
begin
	if not point_id(t^.t.p1^.p,p1^.p) then
		if not point_id(t^.t.p1^.p,p2^.p) then troisieme_point:=t^.t.p1
		else if not point_id(t^.t.p2^.p,p1^.p) then troisieme_point:=t^.t.p2
		else troisieme_point:=t^.t.p3
	else if not point_id(t^.t.p2^.p,p2^.p) then troisieme_point:=t^.t.p2
		else troisieme_point:=t^.t.p3
end;

function triangles_id(t1,t2:triangle):boolean;
begin
	if (t1.p1=t2.p1) and (t1.p2=t2.p2) and (t1.p3=t2.p3) then triangles_id:=true else triangles_id:=false
end;

function initialiser_lt(t:triangle):lt;
(*initialise la liste de triangles*)
var
	aux:lt;
begin
	new(aux);
	aux^.suiv:=nil;
	aux^.prev:=nil;
	aux^.t:=t;
	initialiser_lt:=aux
end;

function remplir_lt(t:triangle;l:lt):lt;
(*ajoute un élément à la liste de triangle*)
var
	aux:lt;
begin
	new(aux);
	aux^.suiv:=nil;
	aux^.prev:=l;
	aux^.t:=t;
	l^.suiv:=aux;
	remplir_lt:=aux
end;

function ajouter_ordre_lt(t:triangle;l:lt):lt;
(*ajoute un nouvel élément dans l'ordre dans la liste de triangle*)
var
	aux:lt;
begin
	while l^.suiv<>nil do l:=l^.suiv;
	if (l^.t.h.x<t.h.x) or ((l^.t.h.x=t.h.x) and (l^.t.h.y<=t.h.y)) then ajouter_ordre_lt:=remplir_lt(t,l)
	else
	begin
		while l^.prev<>nil do l:=l^.prev;
		while (l^.t.h.x<t.h.x) or ((l^.t.h.x=t.h.x) and (l^.t.h.y<=t.h.y)) do l:=l^.suiv;
		aux:=initialiser_lt(t);
		aux^.prev:=l^.prev;
		if l^.prev<>nil then l^.prev^.suiv:=aux;
		l^.prev:=aux;
		aux^.suiv:=l;
		ajouter_ordre_lt:=aux
	end
(*renvoie le nouvel élément*)
end;

procedure afficher_triangle(t:lt);
(*affiche un triangle sur la sortie standard*)
begin
	if t=nil then writeln('VIDE') else
	begin
		write('S1: ');afficher_point(t^.t.p1^.p);
		write('S2: ');afficher_point(t^.t.p2^.p);
		write('S3: ');afficher_point(t^.t.p3^.p);
		write('H:');afficher_point(t^.t.h)
	end
end;

procedure afficher_triangle_et_voisins(t:lt);
(*affiche un triangle ainsi que tous ses voisins sur la sortie standard*)
begin
	if t=nil then
	begin
	writeln('                 ///////////////////////////////////////');
	writeln('                 ///////////////TRIANGLE////////////////');
	writeln('                 ///////////////////////////////////////');
	afficher_triangle(t);
	end
	else
	begin
	writeln('                 ///////////////////////////////////////');
	writeln('                 ///////////////TRIANGLE////////////////');
	writeln('                 ///////////////////////////////////////');
	afficher_triangle(t);
	writeln('                 ///////////////VOISIN 1////////////////');
	afficher_triangle(t^.t.t1);
	writeln('                 ///////////////VOISIN 2////////////////');
	afficher_triangle(t^.t.t2);
	writeln('                 ///////////////VOISIN 3////////////////');		
	afficher_triangle(t^.t.t3);	
	end
end;
	

procedure afficher_lt(t:lt);
(*affiche une liste de triangle sur la sortie standard*)
var
	i,j:integer;
begin
	writeln('/////////////////////////////////////////////////////////////////////////');
	writeln('////////////////////////TRIANGULATION DE DELAUNAY////////////////////////');
	writeln('/////////////////////////////////////////////////////////////////////////');
	writeln;
	while t^.prev<>nil do t:=t^.prev;
	i:=1;
	while t<>nil do 
	begin
		write('       ');write('************************TRIANGLE ',i,'************************');writeln;
		write('       ');write('     (',t^.t.p1^.p.x,' ,',t^.t.p1^.p.y,' )');writeln;
		write('       ');write('     (',t^.t.p2^.p.x,' ,',t^.t.p2^.p.y,' )');writeln;
		write('       ');write('     (',t^.t.p3^.p.x,' ,',t^.t.p3^.p.y,' )');writeln;
		write('       ');write('*********************************************************');
		j:=i;
		while j<>0 do
		begin
			j:=j div 10;
			write('*')
		end;
		writeln;
		writeln;
		i:=i+1;
		t:=t^.suiv
	end;
	writeln;
	writeln('                                  ***')
end;

(*écrit la liste de triangles sur le fichier*)
procedure ecrire_lt(t:lt);
var
	f:text;
	i,j:integer;
begin
	assign(f,'/mnt/sda4/Documents/Progra/spé2/tipe/files/triangles');
	rewrite(f);
		writeln(f);
		writeln(f,'/////////////////////////////////////////////////////////////////////////');
		writeln(f,'////////////////////////////////TRIANGLES////////////////////////////////');
		writeln(f,'/////////////////////////////////////////////////////////////////////////');
		writeln(f);
		i:=1;
		while t^.prev<>nil do t:=t^.prev;
		while t<>nil do 
		begin
			write(f,'       ');write(f,'************************TRIANGLE ',i,'************************');writeln(f);
			write(f,'       ');write(f,'     (',t^.t.p1^.p.x,' ,',t^.t.p1^.p.y,' )');writeln(f);
			write(f,'       ');write(f,'     (',t^.t.p2^.p.x,' ,',t^.t.p2^.p.y,' )');writeln(f);
			write(f,'       ');write(f,'     (',t^.t.p3^.p.x,' ,',t^.t.p3^.p.y,' )');writeln(f);
			write(f,'       ');write(f,'*********************************************************');
			j:=i;
			while j<>0 do
			begin
				j:=j div 10;
				write(f,'*')
			end;
			writeln(f);
			writeln(f);
			i:=i+1;
			t:=t^.suiv
		end;
		writeln(f,'                                  ***');
	close(f)
end;

procedure ecrire_lt_2D(l:lt);
var
	f:text;
	laux:lt;
	i:integer;
begin
	assign(f,'/mnt/sda4/Documents/Progra/spé2/tipe/files/maple_2D.doc');rewrite(f);
	while l^.prev<>nil do l:=l^.prev;
	laux:=l;
	i:=1;
	
	write(f,'X1:=[');
	while l^.suiv<>nil do
	begin
		write(f,l^.t.p1^.p.x,',');
		i:=i+1;
		l:=l^.suiv;
	end;
	write(f,l^.t.p1^.p.x,']');
	writeln(f,':');

	l:=laux;
	write(f,'Y1:=[');
	while l^.suiv<>nil do
	begin
		write(f,l^.t.p1^.p.y,',');
		l:=l^.suiv;
	end;
	write(f,l^.t.p1^.p.y,']');
	writeln(f,':');

	l:=laux;	
	write(f,'X2:=[');
	while l^.suiv<>nil do
	begin
		write(f,l^.t.p2^.p.x,',');
		l:=l^.suiv
	end;
	write(f,l^.t.p2^.p.x,']');
	writeln(f,':');
	
	l:=laux;	
	write(f,'Y2:=[');
	while l^.suiv<>nil do
	begin
		write(f,l^.t.p2^.p.y,',');
		l:=l^.suiv;
	end;
	write(f,l^.t.p2^.p.y,']');
	writeln(f,':');
	
	l:=laux;	
	write(f,'X3:=[');
	while l^.suiv<>nil do
	begin
		write(f,l^.t.p3^.p.x,',');
		l:=l^.suiv;
	end;
	write(f,l^.t.p3^.p.x,']');
	writeln(f,':');

	l:=laux;
	write(f,'Y3:=[');
	while l^.suiv<>nil do
	begin
		write(f,l^.t.p3^.p.y,',');
		l:=l^.suiv;
	end;
	write(f,l^.t.p3^.p.y,']');
	writeln(f,':');
	
	writeln(f,'L:=NULL:');
	writeln(f,'for i to ',i,'do L:=L,[[X1[i],Y1[i]],[X2[i],Y2[i]],[X3[i],Y3[i]],[X1[i],Y1[i]]] od:');
	writeln(f,'plot([L]);');
	
	close(f)
end;

procedure ecrire_lt_3D(l:lt);
var
	f:text;
	laux:lt;
	i:integer;
	s:string[255];
begin
	writeln('Nom du fichier:');
	readln(s);
	s:='/mnt/sda4/Documents/Progra/spé2/tipe/files/'+s;
	assign(f,s);
	rewrite(f);
	while l^.prev<>nil do l:=l^.prev;
	laux:=l;
	i:=1;
	
	write(f,'X1:=[');
	while l^.suiv<>nil do
	begin
		write(f,l^.t.p1^.p.x,',');
		i:=i+1;
		l:=l^.suiv;
	end;
	write(f,l^.t.p1^.p.x,']');
	writeln(f,':');

	l:=laux;
	write(f,'Y1:=[');
	while l^.suiv<>nil do
	begin
		write(f,l^.t.p1^.p.y,',');
		l:=l^.suiv;
	end;
	write(f,l^.t.p1^.p.y,']');
	writeln(f,':');
	
	l:=laux;
	write(f,'Z1:=[');
	while l^.suiv<>nil do
	begin
		write(f,l^.t.p1^.p.z,',');
		l:=l^.suiv;
	end;
	write(f,l^.t.p1^.p.z,']');
	writeln(f,':');

	l:=laux;	
	write(f,'X2:=[');
	while l^.suiv<>nil do
	begin
		write(f,l^.t.p2^.p.x,',');
		l:=l^.suiv
	end;
	write(f,l^.t.p2^.p.x,']');
	writeln(f,':');
	
	l:=laux;	
	write(f,'Y2:=[');
	while l^.suiv<>nil do
	begin
		write(f,l^.t.p2^.p.y,',');
		l:=l^.suiv;
	end;
	write(f,l^.t.p2^.p.y,']');
	writeln(f,':');
	
	l:=laux;	
	write(f,'Z2:=[');
	while l^.suiv<>nil do
	begin
		write(f,l^.t.p2^.p.z,',');
		l:=l^.suiv;
	end;
	write(f,l^.t.p2^.p.z,']');
	writeln(f,':');
	
	l:=laux;	
	write(f,'X3:=[');
	while l^.suiv<>nil do
	begin
		write(f,l^.t.p3^.p.x,',');
		l:=l^.suiv;
	end;
	write(f,l^.t.p3^.p.x,']');
	writeln(f,':');

	l:=laux;
	write(f,'Y3:=[');
	while l^.suiv<>nil do
	begin
		write(f,l^.t.p3^.p.y,',');
		l:=l^.suiv;
	end;
	write(f,l^.t.p3^.p.y,']');
	writeln(f,':');
	
	l:=laux;
	write(f,'Z3:=[');
	while l^.suiv<>nil do
	begin
		write(f,l^.t.p3^.p.z,',');
		l:=l^.suiv;
	end;
	write(f,l^.t.p3^.p.z,']');
	writeln(f,':');
	
	writeln(f,'L:=NULL:');
	writeln(f,'for i to ',i,'do L:=L,[[X1[i],Y1[i],Z1[i]],[X2[i],Y2[i],Z2[i]],[X3[i],Y3[i],Z3[i]],[X1[i],Y1[i],Z1[i]]] od:');
	writeln(f,'with(plots);');
	writeln(f,'polygonplot3d([L]);');
	
	close(f);
	writeln('Fichier enregistré: ',s)
end;

procedure supprimer_lt(l:lt);
var
	laux:lt;
begin
	while l^.prev<>nil do l:=l^.prev;
	while l<>nil do
	begin
		laux:=l^.suiv;
		dispose(l);
		l:=laux
	end
end;

///////////////////////////////////////////////////////////////////////
//////////////////OPÉRATIONS SUR LES LISTES DE LISTES//////////////////
///////////////////////////////////////////////////////////////////////

function remplir_llpt(l:lpt;ll:llpt):llpt;
var
	llnew:llpt;
begin
	new(llnew);
	llnew^.l:=l;
	llnew^.suiv:=ll;
	remplir_llpt:=llnew
end;

procedure supprimer_llpt(l:llpt);
var
	laux:llpt;
begin
	while l<>nil do
	begin
		laux:=l;
		l:=l^.suiv;
		dispose(laux)
	end
end;

function remplir_llt(l:lt;ll:llt):llt;
var
	llnew:llt;
begin
	new(llnew);
	llnew^.l:=l;
	llnew^.suiv:=ll;
	remplir_llt:=llnew
end;

procedure supprimer_llt(l:llt);
var
	laux:llt;
begin
	while l<>nil do
	begin
		laux:=l;
		l:=l^.suiv;
		dispose(laux)
	end
end;

///////////////////////////////////////////////////////////////////////
///////////////////PROCÉDURES PROPRES À L'ALGORITHME///////////////////
///////////////////////////////////////////////////////////////////////

(*fonctions renvoyant les bornes sup et inf d'un sensemble de points afin d'initialiser les deux premiers triangles*)
function xmin_lpt(l:lpt):real;
var
	x:real;
begin
	while l^.suiv<>nil do l:=l^.suiv;
	x:=l^.p.x;
	while l<>nil do
	begin
		if l^.p.x<x then x:=l^.p.x;
		l:=l^.prev
	end;
	xmin_lpt:=x
end;

function xmax_lpt(l:lpt):real;
var
	x:real;
begin
	while l^.suiv<>nil do l:=l^.suiv;
	x:=l^.p.x;
	while l<>nil do
	begin
		if l^.p.x>x then x:=l^.p.x;
		l:=l^.prev
	end;
	xmax_lpt:=x
end;

function ymin_lpt(l:lpt):real;
var
	y:real;
begin
	while l^.suiv<>nil do l:=l^.suiv;
	y:=l^.p.y;
	while l<>nil do
	begin
		if l^.p.y<y then y:=l^.p.y;
		l:=l^.prev
	end;
	ymin_lpt:=y
end;

function ymax_lpt(l:lpt):real;
var
	y:real;
begin
	while l^.suiv<>nil do l:=l^.suiv;
	y:=l^.p.y;
	while l<>nil do
	begin
		if l^.p.y>y then y:=l^.p.y;
		l:=l^.prev
	end;
	ymax_lpt:=y
end;

procedure initialisation(l:lpt;var lptnew:lpt;var ltnew:lt);
(*initialise les deux premiers triangles*)
var
	p1,p2,p3,p4:point;
	xmin,xmax,ymin,ymax:real;
	t1,t2:triangle;
	l1,l2,l3,l4,l5:lpt;
	
begin
	l5:=copier_lpt(l);
	xmin:=xmin_lpt(l5)-0.1;                 
	xmax:=xmax_lpt(l5)+0.1;             
	ymin:=ymin_lpt(l5)-0.1;                  
	ymax:=ymax_lpt(l5)+0.1;				
	creer_point(xmin,ymin,p1);         
	creer_point(xmin,ymax,p2);         
	creer_point(xmax,ymin,p4);          
	creer_point(xmax+0.1,ymax+0.1,p3);
	lptnew:=initialiser_lpt(p1);
	l1:=lptnew;
	lptnew:=remplir_lpt(p2,lptnew);
	l2:=lptnew;
	lptnew:=remplir_lpt(p3,lptnew);
	l3:=lptnew;
	lptnew:=remplir_lpt(p4,lptnew);
	l4:=lptnew;
	creer_triangle_first(l1,l2,l4,t1);
	creer_triangle_first(l3,l4,l2,t2);
	ltnew:=ajouter_ordre_lt(t2,initialiser_lt(t1));
	ltnew^.t.t1:=ltnew^.prev;
	ltnew^.prev^.t.t1:=ltnew
end;

function bon_cote(p,c:point;d:droite):boolean;
(*vérifie que les points c et p sont du même coté de la droite d*)
var
	a,b:real;
begin
	if equ_droite(d,a,b) then
	begin
		if (p.y-a*p.x-b)*(c.y-a*c.x-b)>0 then bon_cote:=true else bon_cote:=false
	end
	else
	begin
		if (p.x-a)*(c.x-a)>0 then bon_cote:=true else bon_cote:=false
	end
end;

function est_dans_triangle (p:point;t:triangle):boolean;
(*vérifie si le point p est dans le triangle*)
var
	d1,d2,d3:droite;
begin
	d1.p:=t.p2^.p;
	d2.p:=t.p3^.p;
	d3.p:=t.p1^.p;
	d1.v.x:=t.p3^.p.x-t.p2^.p.x;
	d1.v.y:=t.p3^.p.y-t.p2^.p.y;
	d2.v.x:=t.p1^.p.x-t.p3^.p.x;
	d2.v.y:=t.p1^.p.y-t.p3^.p.y;
	d3.v.x:=t.p2^.p.x-t.p1^.p.x;
	d3.v.y:=t.p2^.p.y-t.p1^.p.y;
	est_dans_triangle:=(bon_cote(p,t.p1^.p,d1)) and (bon_cote(p,t.p2^.p,d2)) and (bon_cote(p,t.p3^.p,d3))
end;

function triangle_contenant_p(l:lt;p:point):lt;
(*trouve le triangle contenant le point p*)
var
	test1,test2,test3:boolean;
	d1,d2,d3:droite;
	
begin
	while l^.prev<>nil do l:=l^.prev;
	while not est_dans_triangle(p,l^.t) do
	begin	
		creer_droite(l^.t.p1^.p,l^.t.p2^.p,d3);
		creer_droite(l^.t.p2^.p,l^.t.p3^.p,d1);
		creer_droite(l^.t.p3^.p,l^.t.p1^.p,d2);	
		if not bon_cote(p,l^.t.p1^.p,d1) then l:=l^.t.t1 else
		if not bon_cote(p,l^.t.p2^.p,d2) then l:=l^.t.t2 else
		if not bon_cote(p,l^.t.p3^.p,d3) then l:=l^.t.t3
	end;
	triangle_contenant_p:=l;
end;

function one_two_three(l:lt;p:lpt):lt;
(*transforme un triangle et un point qui est à l'intérieur en un ensemble de trois triangles et supprime le triangle original*)
var
	t1,t2,t3:triangle;
	tl1,tl2,tl3:lt;
begin
	creer_triangle_first(l^.t.p2,l^.t.p3,p,t1);
	creer_triangle_first(l^.t.p3,l^.t.p1,p,t2);
	creer_triangle_first(l^.t.p1,l^.t.p2,p,t3);
	
	tl1:=ajouter_ordre_lt(t1,l);
	tl2:=ajouter_ordre_lt(t2,l);
	tl3:=ajouter_ordre_lt(t3,l);

	tl1^.t.t1:=tl2;
	tl1^.t.t2:=tl3;
	tl1^.t.t3:=l^.t.t1;
	if l^.t.t1<>nil then
	begin
		if l^.t.t1^.t.t1=l then l^.t.t1^.t.t1:=tl1 else
		if l^.t.t1^.t.t2=l then l^.t.t1^.t.t2:=tl1 else
		if l^.t.t1^.t.t3=l then l^.t.t1^.t.t3:=tl1
	end;
	
	tl2^.t.t1:=tl3;
	tl2^.t.t2:=tl1;
	tl2^.t.t3:=l^.t.t2;
	if l^.t.t2<>nil then
	begin
		if l^.t.t2^.t.t1=l then l^.t.t2^.t.t1:=tl2 else
		if l^.t.t2^.t.t2=l then l^.t.t2^.t.t2:=tl2 else
		if l^.t.t2^.t.t3=l then l^.t.t2^.t.t3:=tl2
	end;
	
	tl3^.t.t1:=tl1;
	tl3^.t.t2:=tl2;
	tl3^.t.t3:=l^.t.t3;
	if l^.t.t3<>nil then
	begin
		if l^.t.t3^.t.t1=l then l^.t.t3^.t.t1:=tl3 else
		if l^.t.t3^.t.t2=l then l^.t.t3^.t.t2:=tl3 else
		if l^.t.t3^.t.t3=l then l^.t.t3^.t.t3:=tl3
	end;
	
	if l^.prev<>nil then l^.prev^.suiv:=l^.suiv;
	if l^.suiv<>nil then l^.suiv^.prev:=l^.prev;
	dispose(l);
	
	one_two_three:=tl1
end;

function interieur_cercle(p:point;t:lt):boolean;
(*indique si le point p est à l'intérieur du triangle t*)
var
	d:real;
begin
	if distance_carree(t^.t.h,p)<distance_carree(t^.t.h,t^.t.p1^.p) then interieur_cercle:=true else interieur_cercle:=false
end;

function verif_active(p:lpt;l,v1:lt):lt;
(*procedure principal, s'assure que la triangulation est de Delaunay, et sinon, elle la modifie pour qu'elle le devienne*)
var
	d1,d2,d3:droite;
	t1,t2:triangle;
	v2,v3,v4,v5:lt;
	l1,l2,laux:lt;
begin
	if l=nil then verif_active:=l (*cas plancher*)
	else
	begin
		if not interieur_cercle(p^.p,l) then verif_active:=l
		else
		begin
			(*créations*)
			creer_droite(l^.t.p2^.p,l^.t.p3^.p,d1);
			creer_droite(l^.t.p3^.p,l^.t.p1^.p,d2);
			creer_droite(l^.t.p1^.p,l^.t.p2^.p,d3);
			
			if not bon_cote(p^.p,l^.t.p1^.p,d1) then
			begin
				creer_triangle_first(l^.t.p1,l^.t.p2,p,t1);
				creer_triangle_first(l^.t.p1,l^.t.p3,p,t2);
			
				l1:=ajouter_ordre_lt(t1,l);
				l2:=ajouter_ordre_lt(t2,l);
				
				v2:=voisin_arrete(v1,p,l^.t.p2);
				v3:=voisin_arrete(v1,p,l^.t.p3);
				
				v4:=l^.t.t3;
				v5:=l^.t.t2
			end
		
			else if not bon_cote(p^.p,l^.t.p2^.p,d2) then
			begin
				creer_triangle_first(l^.t.p2,l^.t.p1,p,t1);
				creer_triangle_first(l^.t.p2,l^.t.p3,p,t2);
			
				l1:=ajouter_ordre_lt(t1,l);
				l2:=ajouter_ordre_lt(t2,l);
			
				v2:=voisin_arrete(v1,p,l^.t.p1);			
				v3:=voisin_arrete(v1,p,l^.t.p3);
				
				v4:=l^.t.t3;
				v5:=l^.t.t1
			end
		
			else if not bon_cote(p^.p,l^.t.p3^.p,d3) then
			begin
				creer_triangle_first(l^.t.p3,l^.t.p2,p,t1);
				creer_triangle_first(l^.t.p3,l^.t.p1,p,t2);
			
				l1:=ajouter_ordre_lt(t1,l);
				l2:=ajouter_ordre_lt(t2,l);

				v2:=voisin_arrete(v1,p,l^.t.p2);
				v3:=voisin_arrete(v1,p,l^.t.p1);
				
				v4:=l^.t.t1;
				v5:=l^.t.t2
			end
			
			else write('alert');
		
			(*affectations a*)
			l1^.t.t1:=v2;
			l1^.t.t2:=l2;
			l1^.t.t3:=v4;
		
			l2^.t.t1:=v3;
			l2^.t.t2:=l1;
			l2^.t.t3:=v5;
			
			(*affectation b*)
			if v2<>nil then
			begin
				if v2^.t.t1=v1 then v2^.t.t1:=l1
				else if v2^.t.t2=v1 then v2^.t.t2:=l1
				else if v2^.t.t3=v1 then v2^.t.t3:=l1
			end;
		
			if v3<>nil then
			begin
				if v3^.t.t1=v1 then v3^.t.t1:=l2
				else if v3^.t.t2=v1 then v3^.t.t2:=l2
				else if v3^.t.t3=v1 then v3^.t.t3:=l2
			end;			

			if v4<>nil then
			begin
				if v4^.t.t1=l then v4^.t.t1:=l1
				else if v4^.t.t2=l then v4^.t.t2:=l1
				else if v4^.t.t3=l then v4^.t.t3:=l1
			end;
		
			if v5<>nil then
			begin
				if v5^.t.t1=l then v5^.t.t1:=l2
				else if v5^.t.t2=l then v5^.t.t2:=l2
				else if v5^.t.t3=l then v5^.t.t3:=l2
			end;
			
			(*suppressions*)
			if v1^.prev<>nil then v1^.prev^.suiv:=v1^.suiv;
			if v1^.suiv<>nil then v1^.suiv^.prev:=v1^.prev;
			dispose(v1);

			
			if l^.prev<>nil then l^.prev^.suiv:=l^.suiv;
			if l^.suiv<>nil then l^.suiv^.prev:=l^.prev;
			dispose(l);
			
			(*récurrences*)
			
			laux:=verif_active(p,v4,l1);
			laux:=verif_active(p,v5,l2);
			
			verif_active:=l1
		end
	end
end;

function ajoute_point_graphe(p:lpt;l:lt):lt;
(*ajoute un point au maillage et modifie le maillage*)
var
	t1,t2,t3,tnew:lt;
begin
	t1:=one_two_three(triangle_contenant_p(l,p^.p),p);
	
	t2:=t1^.t.t1;
	t3:=t1^.t.t2;

	t1:=verif_active(p,t1^.t.t3,t1);
	t2:=verif_active(p,t2^.t.t3,t2);
	t3:=verif_active(p,t3^.t.t3,t3);
	
	ajoute_point_graphe:=t1;
end;

procedure pre_supprime_boite(t_ini:lt;var ll:llt;ext,int,boite:lpt;var pp:llpt;test:boolean);
var
	p3:lpt;
begin
	if (ll^.l<>t_ini) or (test) then
	begin
		p3:=troisieme_point(ll^.l,ext,int);
		if appartient_lpt(p3,boite) then (*si p3 est à l'extérieur*)
		begin
			ll:=remplir_llt(voisin_arrete(ll^.l,p3,int),ll);
			pre_supprime_boite(t_ini,ll,p3,int,boite,pp,false)
		end
		else 
		begin
			pp:=remplir_llpt(p3,pp);
			ll:=remplir_llt(voisin_arrete(ll^.l,ext,p3),ll);
			pre_supprime_boite(t_ini,ll,ext,p3,boite,pp,false);
		end
	end
end;
			
procedure nettoyage_lt(l:llt);
begin
	while l<>nil do
	begin
		if l^.l^.prev<>nil then l^.l^.prev^.suiv:=l^.l^.suiv;
		if l^.l^.suiv<>nil then l^.l^.suiv^.prev:=l^.l^.prev;
		l:=l^.suiv;
	end
end;

function supprime_boite(l:lt;p:lpt):lt;
(*supprime la boite englobante*)
var
	test:boolean;
	p1,p2,p3,p4,p5,p6:lpt;
	c:point;
	d1,d2:droite;
	t:triangle;
	liste,liste_aux:llpt;
	ll1:llt;
	l1:lt;
begin
	(*on affecte les points de la boite*)
	while p^.prev<>nil do p:=p^.prev;
	p1:=p;	
	p:=p^.suiv;
	p2:=p;
	p:=p^.suiv;
	p3:=p;
	p:=p^.suiv;
	p4:=p;
	
	(*création du point central du mayage*)
	creer_droite(p1^.p,p3^.p,d1);creer_droite(p2^.p,p4^.p,d2);point_intersection_droite(d1,d2,c);
	
	(*on récupère un triangle ne contenant qu'un seul sommet de la boite*)
	while l^.prev<>nil do l:=l^.prev;
	test:=false;
	if ((l^.t.p1=p1) and (l^.t.p2<>p2) and (l^.t.p2<>p3) and (l^.t.p3<>p2) and (l^.t.p2<>p3))
			or ((l^.t.p1=p2) and (l^.t.p2<>p1) and (l^.t.p2<>p3) and (l^.t.p3<>p1) and (l^.t.p2<>p3))
			or ((l^.t.p1=p3) and (l^.t.p2<>p1) and (l^.t.p2<>p2) and (l^.t.p3<>p1) and (l^.t.p2<>p2))
			then test:=true;
	while not test do
	begin
		l:=l^.suiv;
		if ((l^.t.p1=p1) and (l^.t.p2<>p2) and (l^.t.p2<>p3) and (l^.t.p3<>p2) and (l^.t.p2<>p3))
			or ((l^.t.p1=p2) and (l^.t.p2<>p1) and (l^.t.p2<>p3) and (l^.t.p3<>p1) and (l^.t.p2<>p3))
			or ((l^.t.p1=p3) and (l^.t.p2<>p1) and (l^.t.p2<>p2) and (l^.t.p3<>p1) and (l^.t.p2<>p2))
			then test:=true;
		if l=nil then write('problème récupère');
	end;
	ll1:=remplir_llt(l,nil);
	
	(*création des listes de triangles à supprimer et des points coutours du maillage*)
	if appartient_lpt(l^.t.p1,p) then 
	begin
		p5:=l^.t.p1;
		p6:=l^.t.p2;
		l1:=l^.t.t1;
		liste:=remplir_llpt(p6,nil)
	end
	else if appartient_lpt(l^.t.p2,p) then
	begin
		p5:=l^.t.p2;
		p6:=l^.t.p3;
		l1:=l^.t.t2;
		liste:=remplir_llpt(p6,nil)
	end
	else if appartient_lpt(l^.t.p3,p) then
	begin
		p5:=l^.t.p3;
		p6:=l^.t.p1;
		l1:=l^.t.t3;
		liste:=remplir_llpt(p6,nil)
	end
	else writeln('error supprime_boite');
	liste_aux:=liste;
	pre_supprime_boite(l,ll1,p5,p6,p,liste,true);

	(*suppression des triangles*)
	nettoyage_lt(ll1);

	(*création d'une enveloppe convexe*)
	if liste^.l=p6 then liste:=liste^.suiv;
	liste_aux^.suiv:=liste;
	liste_aux:=liste;
	test:=false;
	while (liste<>liste_aux) or (not test) do
	begin
		test:=true;
		p1:=liste^.l;
		p2:=liste^.suiv^.l;
		p3:=liste^.suiv^.suiv^.l;
		creer_droite(p1^.p,p3^.p,d1);
		if bon_cote(p2^.p,c,d1) then
		begin
			creer_triangle_first(p1,p2,p3,t);
			l1:=ajouter_ordre_lt(t,l1);
			liste_aux:=liste^.suiv;
			liste^.suiv:=liste_aux^.suiv;
			dispose(liste_aux);
			liste_aux:=liste^.suiv;
			liste:=liste^.suiv;
			test:=false
		end;
		liste:=liste^.suiv
	end;
	supprime_boite:=l1
end;

///////////////////////////////////////////////////////////////////////
/////////////////////////ALGORITHME DE DELAUNAY////////////////////////
///////////////////////////////////////////////////////////////////////

function alg_delaunay(p:lpt):lt;
var
	t:lt;
	lnew:lpt;
begin
	initialisation(p,lnew,t);
	
	while p^.prev<>nil do p:=p^.prev;
	
	while p<>nil do
	begin
		t:=ajoute_point_graphe(p,t);
		p:=p^.suiv
	end;
	
	alg_delaunay:=supprime_boite(t,lnew)^.suiv
end;

///////////////////////////////////////////////////////////////////////
//////////////////////////GESTION DES EXEMPLES/////////////////////////
///////////////////////////////////////////////////////////////////////

function remplir_exemple:lpt;
var
	x,y:real;
	p:point;
	l:lpt;
	s:string[255];
begin
	writeln('x?');readln(x);
	writeln('y?');readln(y);
	p.x:=x;p.y:=y;
	l:=initialiser_lpt(p);
	s:='y';
	while s='y' do
	begin
		writeln('x?');readln(x);
		writeln('y?');readln(y);
		p.x:=x;p.y:=y;
		l:=remplir_lpt(p,l);
		writeln('continue?');readln(s)
	end;
	remplir_exemple:=l
end;

function exemple_lpt:lpt;
var	
	i,n1,n2,n3:integer;
	p:point;
	l:lpt;
begin
	randomize;
	n1:=random(NMAX*10);
	n2:=random(NMAX*10);
	n3:=random(10);
	p.x:=n1;
	p.y:=n2;
	p.z:=n1*n1-n2*n2;
	l:=initialiser_lpt(p);
	for i:=1 to NMAX do
	begin
		n1:=random(NMAX*10);
		n2:=random(NMAX*10);
		n3:=random(10);
		p.x:=n1;
		p.y:=n2;
		p.z:=n1*n1-n2*n2;
		l:=remplir_lpt(p,l)	
	end;
	exemple_lpt:=l
end;

function exemple_lpt_2:lpt;
var	
	i,n1,n2:integer;
	p:point;
	l:lpt;
begin
	p.x:=2;
	p.y:=3;
	l:=initialiser_lpt(p);
	
	p.x:=4.5;
	p.y:=2;
	l:=remplir_lpt(p,l);

	p.x:=7;
	p.y:=3.5;
	l:=remplir_lpt(p,l);
	
	p.x:=5;
	p.y:=4.5;
	l:=remplir_lpt(p,l);
	
	p.x:=3.5;
	p.y:=7;
	l:=remplir_lpt(p,l);
	
	p.x:=8;
	p.y:=8;
	l:=remplir_lpt(p,l);
	
	exemple_lpt_2:=l
end;

///////////////////////////////////////////////////////////////////////
//////////////////////////PRROGRAMME PRINCIPAL/////////////////////////
///////////////////////////////////////////////////////////////////////

BEGIN
	l:=exemple_lpt;
	del:=alg_delaunay(l);
	
	l_save:=l;
	del_save:=del;
	
//	afficher_lpt(l);
//	ecrire_lpt(l);

//	afficher_lt(del);
//	ecrire_lt(del);
//	ecrire_lt_2D(del);
	ecrire_lt_3D(del);

	supprimer_lpt(l_save);
	supprimer_lt(del_save);

writeln('fin')
END.
