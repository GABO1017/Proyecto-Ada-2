int: n; %numero de equipos
int: Min;
int: Max;
array[1..n, 1..n] of int: D; %matriz de distancias
int: dates;
dates = 2*(n-1);

%inicio variables
array[1..dates, 1..n] of var int: PF;
array[1..dates, 1..n] of var 0..Max: Giras;
array[1..dates, 1..n] of var 0..Max: Permanencias;  
var int: costosGiras;
%fin variables


constraint forall(i in 1..dates) (forall(j in 1..n) (PF[i,j] >= -n /\ PF[i,j] <= n /\ PF[i,j] != 0)); % //las variables de desicion podran tomar valores desde 1 hasta n tanto positivos como negativos.

constraint forall(i in 1..dates-1) (forall(j in 1..n) (abs(PF[i,j]) != abs(PF[i+1,j]))); %// no pueden haber dos partidos iguales consecutivamente

constraint forall(j in 1..n) (sum(i in 1..dates)(PF[i,j] < 0) == n-1 /\ sum(i in 1..dates)(PF[i,j] > 0) == n-1); % //un equipo debe jugar de local y de visitante la misma cantidad de veces

constraint forall(i in 1..n) (forall(j1, j2 in 1..n where j1<j2) (PF[i,j1] != PF[i, j2]) ) ; % //no pueden haber dos partidos iguales en una misma fecha

constraint forall(j in 1..n) (forall(i1,i2 in 1..dates where i1<i2) (PF[i1,j] != PF[i2, j])); % //cada equipo solo puede enfrentarse a otro equipo dos veces, una como local y otra como visitante.

constraint forall(i in 1..dates, j in 1..n) (
   if PF[i,j] < 0 then PF[i, abs(PF[i,j])] = j            
   else PF[i, PF[i,j]] = -j            
   endif
);%//En cada fecha, si un equipo j juega contra un equipo k de visitante, entonces el equipo k jugara contra el equipo j pero k siendo el local y visceversa. 

constraint forall(i in 1..dates, j in 1..n) (
  if PF[i,j] > 0 then
    if i == 1 then Permanencias[i,j] = 1
    else Permanencias[i,j] = Permanencias[i-1, j] +1
    endif
  else Permanencias[i,j] = 0  
  endif
);%Permanencias en su dominio solo podra tomar valores de 0 hasta Max asegurando que un equipo solo este en permanencia hasta Max veces.

constraint forall(i in 1..dates, j in 1..n) (
  if PF[i,j] < 0 then
    if i == 1 then Giras[i,j] = 1
    else Giras[i,j] = Giras[i-1, j] +1
    endif
  else Giras[i,j] = 0  
  endif
);%Giras en su dominio solo podra tomar valores de 0 hasta Max asegurando que un equipo solo este de gira hasta Max veces.

constraint forall(j in 1..n, i in 2..dates)(
if i == dates then 
  if PF[i,j] < 0 then 
  Giras[i,j]>=Min
  else true
  endif
else
  if (PF[i,j] > 0)then 
    if(PF[i-1,j] < 0)
    then Giras[i-1,j]>=Min  
    else true            
    endif   
  else true            
  endif
endif            
);%Las giras consecutivas no pueden ser menores que Min


constraint forall(j in 1..n, i in 2..dates)(
  if i == dates then 
    if PF[i,j] > 0 then 
    Permanencias[i,j] >= Min
    else true
    endif
  else
    if PF[i,j] < 0 then 
      if PF[i-1,j] > 0 then 
      Permanencias[i-1,j] >= Min
      else true              
      endif
    else true               
    endif
  endif        
);%Las permanencias consecutivas no pueden ser menores que Min


%FUNCION OBJETIVO
constraint costosGiras = sum([
if i == 1 then 
  if PF[i,j] < 0 then D[j, abs(PF[i,j])]
  else 0
  endif
elseif i == dates then 
  if PF[i-1,j] < 0 then 
    if PF[i,j] > 0 then D[abs(PF[i-1, j]), j]
    else  D[abs(PF[i-1, j]), abs(PF[i,j])] + D[abs(PF[i,j]), j]
    endif
  else 
    if PF[i,j] > 0 then 0
    else D[j, abs(PF[i,j])] + D[abs(PF[i,j]), j]
    endif    
  endif  
else 
  if PF[i-1,j] < 0 then 
    if PF[i,j] > 0 then D[abs(PF[i-1, j]), j]
    else  D[abs(PF[i-1, j]), abs(PF[i,j])]
    endif
  else 
    if PF[i,j] > 0 then 0
    else D[j, abs(PF[i,j])]
    endif    
  endif    
endif
| 
j in 1..n, i in 1..dates
]);

%solve satisfy;
solve minimize costosGiras;

output["Costo: \(costosGiras) , Matriz: \(PF)"]