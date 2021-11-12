(defmodule MAIN (export ?ALL))

(deftemplate exec
   (slot step)
   (slot action (allowed-values fire guess unguess solve))
   (slot x) ;;non usato nel caso del comando solve
   (slot y) ;;non usato nel caso del comando solve
)
(deftemplate status (slot step) (slot currently (allowed-values running stopped)) )

(deftemplate moves (slot fires) (slot guesses) )

(deftemplate statistics
	(slot num_fire_ok)
	(slot num_fire_ko)
	(slot num_guess_ok)
	(slot num_guess_ko)
	(slot num_safe)
	(slot num_sink)
)
;-------------------------------------------------------------------------------
;dimensione mappa di gioco, può essere usata in alternativa al light-cell
(deftemplate map-size
  (slot max-depth)
  (slot max-length)
  (slot startX)
  (slot startY)
)
;;serve ad AGENT per non andare fuori dalla tabella
(deftemplate light-cell
	(slot x)
	(slot y)
)

(defrule initialize-light-cell (declare (salience 40))
  ?r <- (init-light-cells)
  ?ms <- (map-size (max-depth ?md) (max-length ?ml) (startX ?x) (startY ?y))
=>
  (while (< ?y ?md)
    (while (< ?x ?ml)
      (assert (light-cell (x ?x) (y ?y)))
      (bind ?x (+ ?x 1))
    )
    (bind ?x 0)
    (bind ?y (+ ?y 1))
  )
  (modify ?ms (startX 0) (startY 0))
  (retract ?r)
)
;-------------------------------------------------------------------------------
(defrule go-on-env-first (declare (salience 30))
  ?f <- (first-pass-to-env)
=>
  (retract ?f)
  (open "log-file.txt" log-file "w")
  (focus ENV)
)

(defrule go-on-agent  (declare (salience 20))
   (maxduration ?d)
   (status (step ?s&:(< ?s ?d)) (currently running))
 =>
    ;(printout t crlf crlf)
    ;(printout t "vado ad agent  step" ?s)
    (focus AGENT)
)

; SI PASSA AL MODULO ENV DOPO CHE AGENTE HA DECISO AZIONE DA FARE
(defrule go-on-env  (declare (salience 30))
  ?f1<-	(status (step ?s))
  (exec (step ?s)) 	;// azione da eseguire al passo s, viene simulata dall'environment
=>
  ; (printout t crlf crlf)
  ; (printout t "vado ad ENV  step" ?s)
  (focus ENV)
)

(defrule game-over
	(maxduration ?d)
	(status (step ?s&:(>= ?s ?d)) (currently running))
=>
	(assert (exec (step ?s) (action solve)))
  (close log-file)
	(focus ENV)
)

(deffacts initial-facts
	(maxduration 100) ;;mosse totali
  (map-size (max-depth 10) (max-length 10) (startX 0) (startY 0))
  (first-pass-to-env)
  (init-light-cells)
	(status (step 0) (currently running))
  (statistics (num_fire_ok 0) (num_fire_ko 0) (num_guess_ok 0) (num_guess_ko 0) (num_safe 0) (num_sink 0))
	(moves (fires 5) (guesses 20))
)
