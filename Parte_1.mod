#
# Escoger las posibles rutas para llevar a todos los alumnos al colegio-Parte 1
#

/* set paradas y estaciones(paradas sin colegio y parking) */
set PARADAS;
set ESTACIONES within PARADAS;
#Se crean sets para los casos especificos del prking y el colegio
set PARK within PARADAS;
set COL within PARADAS;
#Se anaden dos sets para comprobar que la combinacion de sus indices no genere bucles
set DIAGONAL_INVERSA_FILA within PARADAS;
set DIAGONAL_INVERSA_COLUMNA within PARADAS;

/* parametros */
#Se define una matriz que contiene los km de cada recorrido 
param costes {i in PARADAS, j in PARADAS};
#Se definen las personas que esperan en cada parada
param personas_parada {i in PARADAS};
#Se define el total de personas
param personas_total;
#se define la capacidad de los buses
param capacidad;

/* decision variables */
#Se definen las variables que indican que recorrido está siendo usado
var aristas {i in PARADAS, j in PARADAS} binary;
#Se define una matriz que controla el numero de personas que viajan en un recorrido
var flujo {i in PARADAS, j in PARADAS} integer, >=0;

/* objective function */
#Se minimiza el coste, que es de 5 euros por km y de 120 euros por cada autobus
minimize Protfit {k in PARK} : sum{i in PARADAS, j in PARADAS}(costes[i,j]*aristas[i,j]*5) + (sum{i in PARADAS} aristas[k,i]*120);

/* Constraints */
#Sale como mínimo 1 autobús
s.t. Autobus_minimo {k in PARK} : 1 <= sum{i in PARADAS} aristas[k,i];
#Salen como máximo 3 autobuses
s.t. Autobus_maximo {k in PARK} : 3 >= sum{i in PARADAS} aristas[k,i];
#Los que salen del parking son los que llegan al colegio
s.t. Salida_igual_llegada {k in PARK, t in COL} : sum{i in PARADAS} aristas[k,i] = sum{i in PARADAS} aristas[i,t];

#A cada parada llega 1 autobus como maximo
s.t. Llegada_a_parada {k in ESTACIONES} : 1 >= sum{i in PARADAS} aristas[i,k]; 

#Los autobuses que llegan a una parada son los mismos que salen de esta
s.t. Salida_de_parada {k in ESTACIONES} : sum{i in PARADAS} aristas[k,i] = sum{i in PARADAS} aristas[i,k];

#Al parking no llegan personas
s.t. Flujo_llegada_parking  {k in PARK}: sum{i in PARADAS} flujo[i,k] = 0;

#El nuevo flujo de ir a otra parada, menos el que habia llegado, menos las nuevas personas que se van a agregar tiene que ser 0
s.t. Flujo_parada {k in ESTACIONES} : sum{i in PARADAS}( flujo[k,i] - flujo[i,k] - aristas[k,i] * personas_parada[i]) = 0;

#Al colegio tienen que llegar todos los alumnos
s.t. Flujo_llegada_colegio {k in COL} : sum{i in PARADAS} flujo[i,k] = personas_total;

#Al parking no llega ningun autobus
s.t. Autobuses_llegada_parking {k in PARK} : sum{i in PARADAS} aristas[i,k] = 0;

#No salen autobuses del colegio 
s.t. Autobuses_salida_colegio {k in COL} : sum{i in PARADAS} aristas[k,i] = 0;

#El flujo de ir desde el parking a una parada debe ser el número de personas esperando en esa parada
s.t. Flujo_F0k {k in PARADAS, t in PARK} : flujo[t,k] = aristas[t,k]*personas_parada[k];

#El flujo de ir de una parada a otra no puede superar la capacidad de los autobuses
s.t. Flujo_maximo_Sk {k in ESTACIONES} : capacidad >= sum{i in PARADAS} flujo[k,i];

#No se puede volver de la parada de la que se acaba de llegar
s.t. Sin_bucle {i in DIAGONAL_INVERSA_FILA, j in DIAGONAL_INVERSA_COLUMNA : i<>j} : 1>= aristas[i,j]+aristas[j,i];

#No salen alumnos del colegio
s.t. Flujo_salida_colegio {k in COL} : sum{i in PARADAS} flujo[k,i] = 0;

#Si no llegan alumnos al colegio desde una parada, el flujo de esta combinación es 0
s.t. Flujo_llegada_Fk4 {k in ESTACIONES, t in COL} : flujo[k,t] <= aristas[k,t] * 100;

#Si un autobus recorre una arista, su flujo debe ser como minimo el numero de personas esperando en la parada posterior
s.t. Flujo_Sk_a_St_may {k in ESTACIONES, t in ESTACIONES} : flujo[k,t] >= aristas[k,t] * personas_parada[t];

#Si no llegan alumnos a una parada desde otra parada, el flujo de esta combinación es 0
s.t. Flujo_Sk_a_St_men {k in ESTACIONES, t in ESTACIONES} : flujo[k,t] <= aristas[k,t] * 100;

end;
