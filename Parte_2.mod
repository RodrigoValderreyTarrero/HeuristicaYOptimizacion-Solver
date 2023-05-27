#
# Escoger las posibles rutas para llevar a todos los alumnos al colegio - Parte 2
#

/* set paradas (y esatciones que no son el colegio o el parking) y alumnos*/
set PARADAS;
set ALUMNOS;
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
#Se define a que paradas puede ir cada alumno
param disponibilidad{i in ALUMNOS, j in PARADAS};
#Se define el parametro que indica quienes son hermanos
param hermanos {i in ALUMNOS, j in ALUMNOS};
#Se define el total de personas
param personas_total;
#se define la capacidad de los buses
param capacidad;

/* decision variables */
#Se definen las variables que indican que recorrido está siendo usado
var aristas {i in PARADAS, j in PARADAS} binary;
#Se define una matriz que controla el numero de personas que viajan en un recorrido
var flujo {i in PARADAS, j in PARADAS} integer, >=0;
#se define la matriz que indica en que parada espera cada uno
var personas_parada{i in ALUMNOS, j in PARADAS} binary;

/* objective function */
#Se minimiza el coste, que es de 5 euros por km y de 120 euros por cada autobus
minimize Protfit {k in PARK}: sum{i in PARADAS, j in PARADAS}(costes[i,j]*aristas[i,j]*5) + (sum{i in PARADAS} aristas[k,i]*120);

/* Constraints */
#se comprueba que no haya mas personas esperando que las que caben en un autobus
s.t. suma_columna {k in PARADAS} : sum{i in ALUMNOS}personas_parada[i,k] <= capacidad;

#Se asigna una parada a cada alumno de las que tiene disponibles
s.t. parada_asignada {k in ALUMNOS}: sum{i in PARADAS}personas_parada[k,i]*disponibilidad[k,i] = 1;

#No se pueden asignar paradas que no esten dsiponibles
s.t. no_asignar_no_disponibles {k in ALUMNOS} : sum{i in PARADAS}personas_parada[k,i] = 1;

#Si dos alumnos son hermanos se deben encontrar en la misma parada
s.t. comprobar_hermanos_S1 {i in ALUMNOS, j in ALUMNOS, t in PARADAS}:(personas_parada[i,t]-personas_parada[j,t])*hermanos[i,j] = 0;

#Sale como minimo 1 autobus
s.t. Autobus_minimo {k in PARK} : 1 <= sum{i in PARADAS} aristas[k,i];
#Salen como maximo 3 autobuses
s.t. Autobus_maximo {k in PARK} : 3 >= sum{i in PARADAS} aristas[k,i];
#Los que salen del parking son los que llegan al colegio
s.t. Salida_igual_llegada {k in PARK, t in COL}: sum{i in PARADAS} aristas[k,i] = sum{i in PARADAS} aristas[i,t];

#A cada parada llega 1 autobus como maximo
s.t. Llegada_a_parada {k in ESTACIONES}: 1 >= sum{i in PARADAS} aristas[i,k]; 

#Los autobuses que llegan a una parada son los mismos que salen de esta
s.t. Salida_de_parada {k in ESTACIONES} : sum{i in PARADAS} aristas[k,i] = sum{i in PARADAS} aristas[i,k];
#Al parking no llegan personas
s.t. Flujo_llegada_parking {k in PARK} : sum{i in PARADAS} flujo[i,k] = 0;

#Al colegio tienen que llegar todos los alumnos
s.t. Flujo_llegada_colegio {k in COL} : sum{i in PARADAS} flujo[i,k] = personas_total;

#Al parking no llega ningun autobus
s.t. Autobuses_llegada_parking {k in PARK} : sum{i in PARADAS} aristas[i,k] = 0;

#No salen autobuses del colegio 
s.t. Autobuses_salida_colegio {k in COL} : sum{i in PARADAS} aristas[k,i] = 0;

#El flujo de personas que sale del parking es como maximo el numero de personas esperando a la que van
s.t. flujo_parking_men {k in PARADAS, t in PARK} : flujo[t,k] <= sum{i in ALUMNOS}personas_parada[i,k];

#El flujo de personas que sale del parking debe ser tan grande como las personas esperando en esa parada
s.t. flujo_parking_may {k in PARADAS, t in PARK} : 20 >= aristas[t,k]*20 + sum{i in ALUMNOS}personas_parada[i,k] - flujo[t,k];

#Si no salen rutas del parking hacia una parada, el flujo de personas en ese trayecto es 0
s.t. flujo_parking_0 {k in PARADAS, t in PARK} : flujo[t,k] <= aristas[t,k]*100;

/*El flujo de personas para ir de una parada a otra,si se va a esa parada debe ser tan grande como para 
igualar las personas esperando en la nueva parada como las que lleva ya el bus*/
s.t. flujo_Sk_St {k in ESTACIONES, t in ESTACIONES} : 20 >= aristas[k,t]*20 + sum{i in ALUMNOS}personas_parada[i,t] + sum{i in PARADAS}aristas[i,k] - flujo[k,t];

#Al colegio debe llegar como maximo el numero de personas que había en la anterior parada
s.t. flujo_llegada_colegio {k in ESTACIONES, t in COL} : flujo[k,t] <= sum{i in PARADAS}flujo[i,k];

#El flujo de ir de una parada a otra no puede superar la capacidad de los autobuses
s.t. Flujo_maximo_Sk {k in ESTACIONES} : capacidad >= sum{i in PARADAS} flujo[k,i];

#No se puede volver de la parada de la que se acaba de llegar
s.t. Sin_bucle {i in DIAGONAL_INVERSA_FILA, j in DIAGONAL_INVERSA_COLUMNA : i<>j} : 1>= aristas[i,j]+aristas[j,i];

#No salen alumnos del colegio
s.t. Flujo_salida_colegio {k in COL} : sum{i in PARADAS} flujo[k,i] = 0;

#Si no llegan alumnos al colegio desde una parada, el flujo de esta combinación es 0
s.t. Flujo_llegada_Fk4 {k in ESTACIONES, t in COL} : flujo[k,t] <= aristas[k,t] * 100;

#Si un autobus recorre una arista, su flujo debe ser como minimo el numero de personas esperando en la parada posterior
s.t. Flujo_Sk_a_St_may {k in ESTACIONES, t in ESTACIONES} : flujo[k,t] >= aristas[k,t];

#Si no llegan alumnos a una parada desde otra parada, el flujo de esta combinación es 0
s.t. Flujo_Sk_a_St_men {k in ESTACIONES, t in ESTACIONES} : flujo[k,t] <= aristas[k,t] * 100;

end;
