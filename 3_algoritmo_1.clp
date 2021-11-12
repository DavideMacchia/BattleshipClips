(defmodule AGENT (import MAIN ?ALL) (import ENV ?ALL) (export ?ALL))

;;per ogni k-cell esiste una d-cell, ma per ogni d-cell NON esiste per forza una k-cell(alcune dedotte)
;;l'algoritmo lavorerà visionando e modificando solo queste, e non k-cell
(deftemplate d-cell
	(slot x)
	(slot y)
	(slot content (allowed-values water left right middle top bot sub))
	(multislot considered (allowed-values TRUE FALSE)) ;serve per evitare loop quando si update di stat-row/col-prob
)
;;informazioni sulle probabilità di trovare qualcosa all'interno di una data casella. ogni casella ha una p-cell
(deftemplate p-cell
	(slot x)
	(slot y)
	(slot prob) ;;0 quando si conosce il valore della casella, =<1 altrimenti
)
;;fatti contenenti le probabilità di trovare un pezzo di nave (stessa probabilità per le celle di ogni riga o di ogni colonna)
(deftemplate stat-col-prob
	(slot col)
	(slot countHits) ;;numero di pezzi di nave scoperte fin'ora nella colonna
	(slot countMiss) ;;numero di caselle acqua scoperte fin'ora nella colonna
	(slot prob) ;;formula probabilità verticale: (NUMDiPezziDiNaveInColonna-countHits) / (NUMCaselleinColonna-(CountMiss)-(countHits))
)
(deftemplate stat-row-prob
	(slot row)
	(slot countHits)
	(slot countMiss)
	(slot prob)
)

;;------------------------------------------------------------------------------
;vari PRINT sul LOG FILE
(defrule print-action (declare (salience 75))
	(exec (step ?s) (action ?a) (x ?x) (y ?y))
=>
	(printout log-file "[STEP:"?s"][ACTION:"?a"]["?x","?y"]." crlf)
)
;;print valori caselle
(defrule print-d-cell (declare (salience 74))
	(light-cell (x ?x) (y ?y))
	(d-cell (x ?x) (y ?y) (content ?t) (considered FALSE FALSE))
=>
	(printout log-file "[info-CELL]["?x","?y","?t"]." crlf)
)
(defrule print-col-cell (declare (salience 72))
	(stat-col-prob (col ?y) (countHits ?ch) (countMiss ?cm) (prob ?prob))
	(k-per-col (col ?y) (num ?n))
=>
	(printout log-file "[STAT-COL][y:"?y","?prob"---"?n","?ch","?cm"]." crlf)
)
(defrule print-row-cell (declare (salience 73))
	(stat-row-prob (row ?x) (countHits ?ch) (countMiss ?cm) (prob ?prob))
	(k-per-row (row ?x) (num ?n))
=>
	(printout log-file "[STAT-ROW][x:"?x","?prob"---"?n","?ch","?cm"]." crlf)
)
(defrule print-p-cell (declare (salience 71))
	(light-cell (x ?x) (y ?y))
	(p-cell (x ?x) (y ?y) (prob ?p))
=>
	(printout log-file "[P-CELL]["?x","?y","?p"]." crlf)
)
;;------------------------------------------------------------------------------
;;regole per la inizializzazione di stat-col/row. Prob è NUMDiPezziInColonna/10
(defrule stat-col-add-new (declare (salience 70))
	(status (step ?s)(currently running))
	(k-per-col (col ?y) (num ?ck))
	(not (stat-col-prob (col ?y)))
=>
	(assert (stat-col-prob (col ?y) (countHits 0) (countMiss 0) (prob (/ ?ck 10))))
)
(defrule stat-row-add-new (declare (salience 70))
	(status (step ?s)(currently running))
	(k-per-row (row ?x) (num ?rk))
	(not (stat-row-prob (row ?x)))
=>
	(assert (stat-row-prob (row ?x) (countHits 0) (countMiss 0) (prob (/ ?rk 10))))
)

;;regole per l'aggiornamento di stat-col/row dopo che una d-cell è stata trovata
(defrule stat-row-prob-update (declare (salience 65))
	(status (currently running))
	?dc <- (d-cell (x ?x) (content ?cont) (considered ?value FALSE))
	(map-size (max-length ?ml))
	(k-per-row (row ?x) (num ?rk))
	?r <- (stat-row-prob (row ?x) (countHits ?rch) (countMiss ?rcm) (prob ?prob&:(> ?prob 0))) ;controllo per evitare di andare oltre lo zero
=>
	(modify ?dc (considered ?value TRUE))
	(if (eq (- ?ml ?rch ?rcm 1) 0) then
		(if (eq ?cont water)
			then (modify ?r (countMiss (+ ?rcm 1)) (prob 0))
			else (modify ?r (countHits (+ ?rch 1)) (prob 0))
		)
		else
		(if (eq ?cont water)
			then (modify ?r (countMiss (+ ?rcm 1)) (prob (/ (- ?rk ?rch) (- ?ml ?rch (+ ?rcm 1)))))
			else (modify ?r (countHits (+ ?rch 1)) (prob (/ (- ?rk (+ ?rch 1)) (- ?ml (+ ?rch 1) ?rcm))))
		)
	)
)
(defrule stat-col-update (declare (salience 65))
	(status (currently running))
	?dc <- (d-cell (y ?y) (content ?cont) (considered FALSE ?value))
	(k-per-col (col ?y) (num ?ck))
	(map-size (max-depth ?md))
	?c <- (stat-col-prob (col ?y) (countHits ?cch) (countMiss ?ccm) (prob ?prob&:(> ?prob 0)))
=>
	(modify ?dc (considered TRUE ?value))
	(if (eq (- ?md ?cch ?ccm 1) 0) then
		(if (eq ?cont water)
			then (modify ?c (countMiss (+ ?ccm 1)) (prob 0))
			else (modify ?c (countHits (+ ?cch 1)) (prob 0))
		)
		else
		(if (eq ?cont water)
			then (modify ?c (countMiss (+ ?ccm 1)) (prob (/ (- ?ck ?cch) (- ?md ?cch (+ ?ccm 1)))))
			else (modify ?c (countHits (+ ?cch 1)) (prob (/ (- ?ck (+ ?cch 1)) (- ?md (+ ?cch 1) ?ccm))))
		)
	)
)

;;------------------------------------------------------------------------------
;;faccio update delle p-cell di celle sconosciute quando stat-row/col subiscono delle modifiche
(defrule update-p-cells (declare (salience 63))
	(status (currently running))
	(stat-row-prob (row ?x) (prob ?px))
	(stat-col-prob (col ?y) (prob ?py))
	;serve affinchè non venga selezionato in loop alla fine quando si usa il guess su cella con prob più alta
	?p <- (p-cell (x ?x) (y ?y) (prob ?prob&:(and (not (= ?prob (/ (+ ?py ?px) 2))) (not (= ?prob 0)))))
=>
	(if (or (= ?px 0) (= ?py 0)) ;;gestisce caso in cui una delle due prob stat-col o row sia zero
		then (modify ?p (prob 0))
		else (modify ?p (prob (/ (+ ?py ?px) 2)))
	)
)

;;regole per la inizializzazione di p-cell
(defrule new-p-cell-from-unknown-d-cell (declare (salience 60))
	(status (currently running))
	(light-cell (x ?x) (y ?y))
	(not (d-cell (x ?x) (y ?y)))
	(not (p-cell (x ?x) (y ?y)))
	(stat-col-prob (col ?y) (prob ?py))
	(stat-row-prob (row ?x) (prob ?px))
=>
	(assert (p-cell (x ?x) (y ?y) (prob (/ (+ ?py ?px) 2)))) ;;FORMULA ProbTotale: (ProbVert+ProbOriz)/2, media tra le due
)
(defrule new-p-cell-from-known-d-cell (declare (salience 60))
	(status (currently running))
	(d-cell (x ?x) (y ?y))
	(not (p-cell (x ?x) (y ?y)))
=>
	(assert (p-cell (x ?x) (y ?y) (prob 0))) ;;setto a 0 la prob perchè conosco il contenuto della casella
)
;;regola per l'aggiornamento di p-cell quando trovo nuova d-cell
(defrule p-cell-update-from-known-d-cell (declare (salience 59))
	(status (currently running))
	(d-cell (x ?x) (y ?y))
	?pc <- (p-cell (x ?x) (y ?y) (prob ?prob&:(> ?prob 0)))
=>
	(modify ?pc (prob 0))
)
;;aggiornamento altre p-cell nella stessa linea e colonna
;;regola per la inizializzazione di nuove d-cell per ogni nuova k-cell
(defrule add-new-d-cell-from-k-cell (declare (salience 55))
	(status (currently running))
	(k-cell (x ?x) (y ?y) (content ?c))
	(not (d-cell (x ?x) (y ?y)))
=>
	(assert (d-cell (x ?x) (y ?y) (content ?c) (considered FALSE FALSE)))
)


;;REGOLE DI DEDUZIONE su caselle il cui contenuto è logicamente ovvio
;;dato che ENV non crea k-cell per la WATER dopo aver usato il FIRE, questa regola crea la corrispondnte d-cell (da eseguire dopo gli update)
(defrule missed-fire-deduce-water (declare (salience 41))
	(status (currently running))
	(exec (action fire) (x ?x) (y ?y)) ;;NON specificare lo step
	(not (k-cell (x ?x) (y ?y))) ;;NON specificare contenuto
	(not (d-cell (x ?x) (y ?y) (content water)))
=>
	(assert (d-cell (x ?x) (y ?y) (content water) (considered FALSE FALSE)))
)
;;------------------------------------------------------------------------------
;;DEDUZIONE caselle WATER attorno (non diagonale) a pezzi di nave che conosciamo (tranne middle)
(defrule deduce-water-on-top (declare (salience 40))
	(status (step ?s)(currently running))
  (d-cell (x ?x) (y ?y) (content sub|top|left|right)) ;;NON deve contenere BOT, perchè potrebbe avere un pezzo di nave in quel punto
	(light-cell (x =(- ?x 1)) (y ?y))
  (not (d-cell (x =(- ?x 1)) (y ?y)))
=>
  (assert (d-cell (x =(- ?x 1)) (y ?y) (content water) (considered FALSE FALSE)))
)
(defrule deduce-water-on-bot (declare (salience 40))
	(status (step ?s)(currently running))
  (d-cell (x ?x) (y ?y) (content sub|bot|left|right))
	(light-cell (x =(+ ?x 1)) (y ?y))
  (not (d-cell (x =(+ ?x 1)) (y ?y)))
=>
  (assert (d-cell (x =(+ ?x 1)) (y ?y) (content water) (considered FALSE FALSE)))
)
(defrule deduce-water-on-left (declare (salience 40))
	(status (step ?s)(currently running))
  (d-cell (x ?x) (y ?y) (content sub|top|bot|left))
	(light-cell (x ?x) (y =(- ?y 1)))
  (not (d-cell (x ?x) (y =(- ?y 1))))
=>
  (assert (d-cell (x ?x) (y =(- ?y 1)) (content water) (considered FALSE FALSE)))
)
(defrule deduce-water-on-right (declare (salience 40))
	(status (step ?s)(currently running))
  (d-cell (x ?x) (y ?y) (content sub|top|bot|right))
	(light-cell (x ?x) (y =(+ ?y 1)))
  (not (d-cell (x ?x) (y =(+ ?y 1))))
=>
  (assert (d-cell (x ?x) (y =(+ ?y 1)) (content water) (considered FALSE FALSE)))
)

;;------------------------------------------------------------------------------
;;DEDUZIONE nave 2 caselle, caso in cui si conoscone un ESTREMO di una nave e spazio insufficente per tre pezzi di nave.
(defrule k-top-deduce-bot (declare (salience 35))
  (status (step ?s)(currently running))
  (d-cell (x ?x) (y ?y) (content top))
  (moves (guesses ?ng&:(> ?ng 0)))
  (or (not (light-cell (x =(+ ?x 2)) (y ?y))) (d-cell (x =(+ ?x 2)) (y ?y) (content water))) ;;casella o NON ESISTE, o si sa che c'è il WATER in essa
  (not (d-cell (x =(+ ?x 1)) (y ?y)))
=>
  (assert (exec (step ?s) (action guess) (x (+ ?x 1)) (y ?y)))
  (assert (d-cell (x =(+ ?x 1)) (y ?y) (content bot) (considered FALSE FALSE)))
  (pop-focus)
)
(defrule k-bot-deduce-top (declare (salience 35))
  (status (step ?s)(currently running))
  (d-cell (x ?x) (y ?y) (content bot))
  (moves (guesses ?ng&:(> ?ng 0)))
  (or (not (light-cell (x =(- ?x 2)) (y ?y))) (d-cell (x =(- ?x 2)) (y ?y) (content water)))
  (not (d-cell (x =(- ?x 1)) (y ?y)))
=>
  (assert (exec (step ?s) (action guess) (x (- ?x 1)) (y ?y)))
  (assert (d-cell (x =(- ?x 1)) (y ?y) (content top) (considered FALSE FALSE)))
  (pop-focus)
)
(defrule k-left-deduce-right (declare (salience 35))
  (status (step ?s)(currently running))
	(moves (guesses ?ng&:(> ?ng 0)))
  (d-cell (x ?x) (y ?y) (content left))
  (or (not (light-cell (x ?x) (y =(+ ?y 2)))) (d-cell (x ?x) (y =(+ ?y 2)) (content water)))
  (not (d-cell (x ?x) (y =(+ ?y 1))))
=>
  (assert (exec (step ?s) (action guess) (x ?x) (y =(+ ?y 1))))
  (assert (d-cell (x ?x) (y =(+ ?y 1)) (content right) (considered FALSE FALSE)))
  (pop-focus)
)
(defrule k-right-deduce-left (declare (salience 35))
  (status (step ?s)(currently running))
  (d-cell (x ?x) (y ?y) (content right))
  (moves (guesses ?ng&:(> ?ng 0)))
  (or (not (light-cell (x ?x) (y =(- ?y 2)))) (d-cell (x ?x) (y =(- ?y 2)) (content water)))
  (not (d-cell (x ?x) (y =(- ?y 1))))
=>
  (assert (exec (step ?s) (action guess) (x ?x) (y =(- ?y 1))))
  (assert (d-cell (x ?x) (y =(- ?y 1)) (content left) (considered FALSE FALSE)))
  (pop-focus)
)

;-------------------------------------------------------------------------------
;DEDUZIONE nave da 3 caselle ORIZZONTALE partendo dai 2 ESTREMI
(defrule k-left-and-right-deduce-middle (declare (salience 33))
  (status (step ?s)(currently running))
  (d-cell (x ?x) (y ?y) (content left))
  (d-cell (x ?x) (y =(+ ?y 2)) (content right))
  (moves (guesses ?ng&:(> ?ng 0)))
  (not (d-cell (x ?x) (y =(+ ?y 1))))
=>
  (assert (exec (step ?s) (action guess) (x ?x) (y (+ ?y 1))))
  (assert (d-cell (x ?x) (y =(+ ?y 1)) (content middle) (considered FALSE FALSE)))
  (pop-focus)
)
;;DEDUZIONE nave da 3 caselle VERTICALE partendo dai 2 ESTREMI
(defrule k-top-and-bot-deduce-middle (declare (salience 33))
  (status (step ?s)(currently running))
  (d-cell (x ?x) (y ?y) (content top))
  (d-cell (x ?x) (y =(+ ?y 2)) (content bot))
  (moves (guesses ?ng&:(> ?ng 0)))
  (not (d-cell (x ?x) (y =(+ ?y 1))))
=>
  (assert (exec (step ?s) (action guess) (x ?x) (y (+ ?y 1))))
  (assert (d-cell (x ?x) (y =(+ ?y 1)) (content middle) (considered FALSE FALSE)))
  (pop-focus)
)
;;DEDUZIONE nave da 4 caselle ORIZZONTALE partendo dai 2 MIDDLE
(defrule k-middle-middle-deduce-left (declare (salience 33))
  (status (step ?s)(currently running))
  (d-cell (x ?x) (y ?y) (content middle))
  (d-cell (x ?x) (y =(- ?y 1)) (content middle))
  (moves (guesses ?ng&:(> ?ng 0)))
  (not (d-cell (x ?x) (y =(- ?y 2))))
=>
  (assert (exec (step ?s) (action guess) (x ?x) (y (- ?y 2))))
  (assert (d-cell (x ?x) (y =(- ?y 2)) (content left) (considered FALSE FALSE)))
  (pop-focus)
)
(defrule k-middle-middle-deduce-right (declare (salience 33))
  (status (step ?s)(currently running))
  (d-cell (x ?x) (y ?y) (content middle))
  (d-cell (x ?x) (y =(+ ?y 1)) (content middle))
  (moves (guesses ?ng&:(> ?ng 0)))
  (not (d-cell (x ?x) (y =(+ ?y 2))))
=>
  (assert (exec (step ?s) (action guess) (x ?x) (y (+ ?y 2))))
  (assert (d-cell (x ?x) (y =(+ ?y 2)) (content right) (considered FALSE FALSE)))
  (pop-focus)
)
;;DEDUZIONE nave da 4 caselle ORIZZONTALE partendo dai 2 ESTREMI
(defrule k-left-and-right-deduce-middle1 (declare (salience 33))
  (status (step ?s)(currently running))
  (d-cell (x ?x) (y ?y) (content left))
  (d-cell (x ?x) (y =(+ ?y 3)) (content right))
  (moves (guesses ?ng&:(> ?ng 0)))
  (not (d-cell (x ?x) (y =(+ ?y 1))))
=>
  (assert (exec (step ?s) (action guess) (x ?x) (y (+ ?y 1))))
  (assert (d-cell (x ?x) (y =(+ ?y 1)) (content middle) (considered FALSE FALSE)))
  (pop-focus)
)
(defrule k-left-and-right-deduce-middle2 (declare (salience 33))
  (status (step ?s)(currently running))
  (d-cell (x ?x) (y ?y) (content left))
  (d-cell (x ?x) (y =(+ ?y 3)) (content right))
  (moves (guesses ?ng&:(> ?ng 0)))
  (not (d-cell (x ?x) (y =(+ ?y 2))))
=>
  (assert (exec (step ?s) (action guess) (x ?x) (y (+ ?y 2))))
  (assert (d-cell (x ?x) (y =(+ ?y 2)) (content middle) (considered FALSE FALSE)))
  (pop-focus)
)
;;DEDUZIONE nave da 4 caselle VERTICALE partendo dai 2 MIDDLE
(defrule k-middle-middle-deduce-top (declare (salience 33))
  (status (step ?s)(currently running))
  (d-cell (x ?x) (y ?y) (content middle))
  (d-cell (x =(- ?x 1)) (y ?y) (content middle))
  (moves (guesses ?ng&:(> ?ng 0)))
  (not (d-cell (x =(- ?x 2)) (y ?y)))
=>
  (assert (exec (step ?s) (action guess) (x (- ?x 2)) (y ?y)))
  (assert (d-cell (x =(- ?x 2)) (y ?y) (content top) (considered FALSE FALSE)))
  (pop-focus)
)
(defrule k-middle-middle-deduce-bot (declare (salience 33))
  (status (step ?s)(currently running))
  (d-cell (x ?x) (y ?y) (content middle))
  (d-cell (x =(+ ?x 1)) (y ?y) (content middle))
  (moves (guesses ?ng&:(> ?ng 0)))
  (not (d-cell (x =(+ ?x 2)) (y ?y)))
=>
  (assert (exec (step ?s) (action guess) (x (+ ?x 2)) (y ?y)))
  (assert (d-cell (x =(+ ?x 2)) (y ?y) (content bot) (considered FALSE FALSE)))
  (pop-focus)
)
;;DEDUZIONE nave da 4 caselle VERTICALE partendo dai 2 ESTREMI
(defrule k-top-and-bot-deduce-middle1 (declare (salience 33))
  (status (step ?s)(currently running))
  (d-cell (x ?x) (y ?y) (content top))
  (d-cell (x =(+ ?x 3)) (y ?y) (content bot))
  (moves (guesses ?ng&:(> ?ng 0)))
  (not (d-cell (x =(+ ?x 1)) (y ?y)))
=>
  (assert (exec (step ?s) (action guess) (x (+ ?x 1)) (y ?y)))
  (assert (d-cell (x =(+ ?x 1)) (y ?y) (content middle) (considered FALSE FALSE)))
  (pop-focus)
)
(defrule k-top-and-bot-deduce-middle2 (declare (salience 33))
  (status (step ?s)(currently running))
  (d-cell (x ?x) (y ?y) (content top))
  (d-cell (x =(+ ?x 3)) (y ?y) (content bot))
  (moves (guesses ?ng&:(> ?ng 0)))
  (not (d-cell (x =(+ ?x 2)) (y ?y)))
=>
  (assert (exec (step ?s) (action guess) (x (+ ?x 2)) (y ?y)))
  (assert (d-cell (x =(+ ?x 2)) (y ?y) (content middle) (considered FALSE FALSE)))
  (pop-focus)
)
;;DEDUZIONE nave da 4 caselle ORIZZONTALE partendo da ESTREMO e MIDDLE
(defrule k-left-and-middle-deduce-middle (declare (salience 32))
  (status (step ?s)(currently running))
  (d-cell (x ?x) (y ?y) (content left))
  (d-cell (x ?x) (y =(+ ?y 2)) (content middle))
  (moves (guesses ?ng&:(> ?ng 0)))
  (not (d-cell (x ?x) (y =(+ ?y 1))))
=>
  (assert (exec (step ?s) (action guess) (x ?x) (y (+ ?y 1))))
  (assert (d-cell (x ?x) (y =(+ ?y 1)) (content middle) (considered FALSE FALSE)))
  (pop-focus)
)
(defrule k-left-and-middle-deduce-right (declare (salience 32))
  (status (step ?s)(currently running))
  (d-cell (x ?x) (y ?y) (content left))
  (d-cell (x ?x) (y =(+ ?y 2)) (content middle))
  (moves (guesses ?ng&:(> ?ng 0)))
  (not (d-cell (x ?x) (y =(+ ?y 3))))
=>
  (assert (exec (step ?s) (action guess) (x ?x) (y (+ ?y 3))))
  (assert (d-cell (x ?x) (y =(+ ?y 3)) (content right) (considered FALSE FALSE)))
  (pop-focus)
)
(defrule k-right-and-middle-deduce-middle (declare (salience 32))
  (status (step ?s)(currently running))
  (d-cell (x ?x) (y ?y) (content right))
  (d-cell (x ?x) (y =(- ?y 2)) (content middle))
  (moves (guesses ?ng&:(> ?ng 0)))
  (not (d-cell (x ?x) (y =(- ?y 1))))
=>
  (assert (exec (step ?s) (action guess) (x ?x) (y (- ?y 1))))
  (assert (d-cell (x ?x) (y =(- ?y 1)) (content middle) (considered FALSE FALSE)))
  (pop-focus)
)
(defrule k-right-and-middle-deduce-left (declare (salience 32))
  (status (step ?s)(currently running))
  (d-cell (x ?x) (y ?y) (content right))
  (d-cell (x ?x) (y =(- ?y 2)) (content middle))
  (moves (guesses ?ng&:(> ?ng 0)))
  (not (d-cell (x ?x) (y =(- ?y 3))))
=>
  (assert (exec (step ?s) (action guess) (x ?x) (y (- ?y 3))))
  (assert (d-cell (x ?x) (y =(- ?y 3)) (content left) (considered FALSE FALSE)))
  (pop-focus)
)
;;DEDUZIONE nave da 4 caselle VERTICALE partendo da ESTREMO e MIDDLE
(defrule k-top-and-middle-deduce-middle (declare (salience 32))
  (status (step ?s)(currently running))
  (d-cell (x ?x) (y ?y) (content top))
  (d-cell (x =(+ ?x 2)) (y ?y) (content middle))
  (moves (guesses ?ng&:(> ?ng 0)))
  (not (d-cell (x =(+ ?x 1)) (y ?y)))
=>
  (assert (exec (step ?s) (action guess) (x (+ ?x 1)) (y ?y)))
  (assert (d-cell (x =(+ ?x 1)) (y ?y) (content middle) (considered FALSE FALSE)))
  (pop-focus)
)
(defrule k-top-and-middle-deduce-bot (declare (salience 32))
  (status (step ?s)(currently running))
  (d-cell (x ?x) (y ?y) (content top))
  (d-cell (x =(+ ?x 2)) (y ?y) (content middle))
  (moves (guesses ?ng&:(> ?ng 0)))
  (not (d-cell (x =(+ ?x 3)) (y ?y)))
=>
  (assert (exec (step ?s) (action guess) (x (+ ?x 3)) (y ?y)))
  (assert (d-cell (x =(+ ?x 3)) (y ?y) (content bot) (considered FALSE FALSE)))
  (pop-focus)
)
(defrule k-bot-and-middle-deduce-middle (declare (salience 32))
  (status (step ?s)(currently running))
  (d-cell (x ?x) (y ?y) (content bot))
  (d-cell (x =(- ?x 2)) (y ?y) (content middle))
  (moves (guesses ?ng&:(> ?ng 0)))
  (not (d-cell (x =(- ?x 1)) (y ?y)))
=>
  (assert (exec (step ?s) (action guess) (x (- ?x 1)) (y ?y)))
  (assert (d-cell (x =(- ?x 1)) (y ?y) (content middle) (considered FALSE FALSE)))
  (pop-focus)
)
(defrule k-bot-and-middle-deduce-top (declare (salience 32))
  (status (step ?s)(currently running))
  (d-cell (x ?x) (y ?y) (content bot))
  (d-cell (x =(- ?x 2)) (y ?y) (content middle))
  (moves (guesses ?ng&:(> ?ng 0)))
  (not (d-cell (x =(- ?x 3)) (y ?y)))
=>
  (assert (exec (step ?s) (action guess) (x (- ?x 3)) (y ?y)))
  (assert (d-cell (x =(- ?x 3)) (y ?y) (content top) (considered FALSE FALSE)))
  (pop-focus)
)

;-------------------------------------------------------------------------------
;caso in cui si conoscono ESTREMI e Water(o fine mappa). DEDUZIONE del resto della nave.
(defrule k-top-and-water-deduce-bot (declare (salience 32))
  (status (step ?s)(currently running))
  (d-cell (x ?x) (y ?y) (content top))
  (or (d-cell (x =(+ ?x 2)) (y ?y) (content water)) (not (light-cell (x =(+ ?x 2)) (y ?y))))
  (moves (guesses ?ng&:(> ?ng 0)))
  (not (d-cell (x =(+ ?x 1)) (y ?y)))
=>
  (assert (exec (step ?s) (action guess) (x (+ ?x 1)) (y ?y)))
  (assert (d-cell (x =(+ ?x 1)) (y ?y) (content bot) (considered FALSE FALSE)))
  (pop-focus)
)
(defrule k-bot-and-water-deduce-top (declare (salience 32))
  (status (step ?s)(currently running))
  (d-cell (x ?x) (y ?y) (content bot))
  (or (d-cell (x =(- ?x 2)) (y ?y) (content water)) (not (light-cell (x =(- ?x 2)) (y ?y))))
  (moves (guesses ?ng&:(> ?ng 0)))
  (not (d-cell (x =(- ?x 1)) (y ?y)))
=>
  (assert (exec (step ?s) (action guess) (x (- ?x 1)) (y ?y)))
  (assert (d-cell (x =(- ?x 1)) (y ?y) (content top) (considered FALSE FALSE)))
  (pop-focus)
)
(defrule k-left-and-water-deduce-right (declare (salience 32))
  (status (step ?s)(currently running))
  (d-cell (x ?x) (y ?y) (content left))
  (or (d-cell (x ?x) (y =(+ ?y 2)) (content water)) (not (light-cell (x ?x) (y =(+ ?y 2)))))
  (moves (guesses ?ng&:(> ?ng 0)))
  (not (d-cell (x ?x) (y =(+ ?y 1))))
=>
  (assert (exec (step ?s) (action guess) (x ?x) (y (+ ?y 1))))
  (assert (d-cell (x ?x) (y =(+ ?y 1)) (content right) (considered FALSE FALSE)))
  (pop-focus)
)
(defrule k-right-and-water-deduce-left (declare (salience 32))
  (status (step ?s)(currently running))
  (d-cell (x ?x) (y ?y) (content right))
  (or (d-cell (x ?x) (y =(- ?y 2)) (content water)) (not (light-cell (x ?x) (y =(- ?y 2)))))
  (moves (guesses ?ng&:(> ?ng 0)))
  (not (d-cell (x ?x) (y =(- ?y 1))))
=>
  (assert (exec (step ?s) (action guess) (x ?x) (y (- ?y 1))))
  (assert (d-cell (x ?x) (y =(- ?y 1)) (content left) (considered FALSE FALSE)))
  (pop-focus)
)

;-------------------------------------------------------------------------------
;;Si CONOSCE ESTREMO, FIRE() a 2 caselle di distanza per dedurre resto della nave
(defrule k-top-fire-two-cells-south (declare (salience 31))
  (status (step ?s)(currently running))
  (d-cell (x ?x) (y ?y) (content top))
  (moves (fires ?fm&:(> ?fm 0)))
  (light-cell (x =(+ ?x 2)) (y ?y))
	(not (d-cell (x =(+ ?x 1)) (y ?y)))
	(not (d-cell (x =(+ ?x 2)) (y ?y)))
=>
  (assert (exec (step ?s) (action fire) (x =(+ ?x 2)) (y ?y)))
  (pop-focus)
)
(defrule k-bot-fire-two-cells-north (declare (salience 31))
  (status (step ?s)(currently running))
  (d-cell (x ?x) (y ?y) (content bot))
  (moves (fires ?fm&:(> ?fm 0)))
  (light-cell (x =(- ?x 2)) (y ?y))
	(not (d-cell (x =(- ?x 1)) (y ?y)))
	(not (d-cell (x =(- ?x 2)) (y ?y)))
=>
  (assert (exec (step ?s) (action fire) (x =(- ?x 2)) (y ?y)))
  (pop-focus)
)
(defrule k-left-fire-two-cells-east (declare (salience 31))
  (status (step ?s)(currently running))
  (d-cell (x ?x) (y ?y) (content left))
  (moves (fires ?fm&:(> ?fm 0)))
  (light-cell (x ?x) (y =(+ ?y 2)))
	(not (d-cell (x ?x) (y =(+ ?y 1))))
  (not (d-cell (x ?x) (y =(+ ?y 2))))
=>
  (assert (exec (step ?s) (action fire) (x ?x) (y =(+ ?y 2))))
  (pop-focus)
)
(defrule k-right-fire-two-cells-ovest (declare (salience 31))
  (status (step ?s)(currently running))
  (d-cell (x ?x) (y ?y) (content right))
  (moves (fires ?fm&:(> ?fm 0)))
  (light-cell (x ?x) (y =(- ?y 2)))
	(not (d-cell (x ?x) (y =(- ?y 1))))
  (not (d-cell (x ?x) (y =(- ?y 2))))
=>
  (assert (exec (step ?s) (action fire) (x ?x) (y =(- ?y 2))))
  (pop-focus)
)
;-------------------------------------------------------------------------------
;;do priorità a cercare nuove navi in posizioni nuove e fare guess per compleatre quelle che già conosco, quindi faccio guess qui invece che fire2
;;questa parte è ampliabile con un meccanismo di deduzione sulla base delle navi già visitate in precedenza
;;caso in cui si conoscono pezzi MIDDLE consecutivi ad un ESTREMO
(defrule k-bot-middle (declare (salience 25))
  (status (step ?s)(currently running))
  (d-cell (x ?x) (y ?y) (content left))
  (d-cell (x =(+ ?x 1)) (y ?y) (content middle))
  (moves (guesses ?fm&:(> ?fm 0)))
	(not (d-cell (x =(+ ?x 2)) (y ?y)))
	?p <- (p-cell (x =(+ ?x 2)) (y ?y))
=>
  (assert (exec (step ?s) (action guess) (x (+ ?x 2)) (y ?y)))
	(modify ?p (prob 0))
  (pop-focus)
)
(defrule k-top-middle (declare (salience 25))
  (status (step ?s)(currently running))
  (d-cell (x ?x) (y ?y) (content right))
  (d-cell (x =(- ?x 1)) (y ?y) (content middle))
  (moves (guesses ?fm&:(> ?fm 0)))
	(not (d-cell (x =(- ?x 2)) (y ?y)))
	?p <- (p-cell (x =(- ?x 2)) (y ?y))
=>
  (assert (exec (step ?s) (action guess) (x (- ?x 2)) (y ?y)))
	(modify ?p (prob 0))
  (pop-focus)
)
(defrule k-left-middle (declare (salience 25))
  (status (step ?s)(currently running))
  (d-cell (x ?x) (y ?y) (content top))
  (d-cell (x ?x) (y =(+ ?y 1)) (content middle))
  (moves (guesses ?fm&:(> ?fm 0)))
	(not (d-cell (x ?x) (y =(+ ?y 2))))
	?p <- (p-cell (x ?x) (y =(+ ?y 2)))
=>
  (assert (exec (step ?s) (action guess) (x ?x) (y (+ ?y 2))))
	(modify ?p (prob 0))
  (pop-focus)
)
(defrule k-right-middle (declare (salience 25))
  (status (step ?s)(currently running))
  (d-cell (x ?x) (y ?y) (content bot))
  (d-cell (x ?x) (y =(- ?y 1)) (content middle))
  (moves (guesses ?fm&:(> ?fm 0)))
	(not (d-cell (x ?x) (y =(- ?y 2))))
	?p <- (p-cell (x ?x) (y =(- ?y 2)))
=>
  (assert (exec (step ?s) (action guess) (x ?x) (y (- ?y 2))))
	(modify ?p (prob 0))
  (pop-focus)
)

;-------------------------------------------------------------------------------
;;caso in cui si conoscono pezzi MIDDLE ISOLATI
(defrule fire-highest-prob-adjacent-middle (declare (salience 25))
  (status (step ?s)(currently running))
  (d-cell (x ?x) (y ?y) (content middle))
	;; controlla che non esistano caselle adiacenti che si conoscono e che siano pezzi di nave
	;;casella Nord o non esiste, o se esiste NON deve avere un pezzo di nave
	(or (and (light-cell (x ?xN&:(eq ?xN (- ?x 1))) (y ?y)) (not (d-cell (x ?xN) (y ?y) (content ~left&~right&~middle&~top&~bot&~sub)))) (not (light-cell (x ?xN&:(eq ?xN (- ?x 1))) (y ?y))))
	(or (and (light-cell (x ?xS&:(eq ?xS (+ ?x 1))) (y ?y)) (not (d-cell (x ?xS) (y ?y) (content ~left&~right&~middle&~top&~bot&~sub)))) (not (light-cell (x ?xS&:(eq ?xS (+ ?x 1))) (y ?y))))
	(or (and (light-cell (x ?x) (y ?yE&:(eq ?yE (+ ?y 1)))) (not (d-cell (x ?x) (y ?yE) (content ~left&~right&~middle&~top&~bot&~sub)))) (not (light-cell (x ?x) (y ?yE&:(eq ?yE (+ ?y 1))))))
	(or (and (light-cell (x ?x) (y ?yO&:(eq ?yO (- ?y 1)))) (not (d-cell (x ?x) (y ?yO) (content ~left&~right&~middle&~top&~bot&~sub)))) (not (light-cell (x ?x) (y ?yO&:(eq ?yO (- ?y 1))))))

	;;seleziono uno degli adiacenti
	(light-cell (x ?x2) (y ?y2))
	(or (and (eq ?x2 =(+ ?x 1)) (eq ?y ?y2)) (and (eq ?x2 =(- ?x 1)) (eq ?y ?y2)) (and (eq ?x ?x2) (eq ?y2 =(+ ?y 1))) (and (eq ?x ?x2) (eq ?y2 =(- ?y 1))))
	(p-cell (x ?x2) (y ?y2) (prob ?prob1))
	;;probabilità più alta tra gli altri adiacenti
	(light-cell (x ?x3) (y ?y3))
  (or (and (eq ?x3 =(+ ?x 1)) (eq ?y ?y3)) (and (eq ?x3 =(- ?x 1)) (eq ?y ?y3)) (and (eq ?x ?x3) (eq ?y3 =(+ ?y 1))) (and (eq ?x ?x3) (eq ?y3 =(- ?y 1))))
	(not (p-cell (x ?x3) (y ?y3) (prob ?prob2&:(> ?prob2 ?prob1))))
=>
  (assert (exec (step ?s) (action fire) (x ?x2) (y ?y2)))
  (pop-focus)
)

(defrule fire-to-high-prob (declare (salience 20))
  (status (step ?s)(currently running))
  (moves (fires ?fm&:(> ?fm 0)))
  ;;seleziona la casella con prob + alta
  (p-cell (x ?x) (y ?y) (prob ?prob1))
  (not (p-cell (prob ?prob2&:(> ?prob2 ?prob1))))
  (not (d-cell (x ?x) (y ?y)))
=>
  ;;spara NELLA cella
  (assert (exec (step ?s) (action fire) (x ?x) (y ?y)))
  (pop-focus)
)

;-------------------------------------------------------------------------------
;;se la prob verticale o quella orizzontale è 1, allora è sicuro che ci sia un pezzo di nave. Sparo guess
(defrule guess-sure-cell (declare (salience 16))
  (status (step ?s) (currently running))
	(light-cell (x ?x) (y ?y))
  (not (d-cell (x ?x) (y ?y)))
  (moves (guesses ?ng&:(> ?ng 0)))
	(stat-col-prob (col ?y) (prob ?py))
	(stat-row-prob (row ?x) (prob ?px))
  ?p <- (p-cell (x ?x) (y ?y))
  (test (or (eq 1 ?px) (eq 1 ?py)))
=>
  (assert (exec (step ?s) (action guess) (x ?x) (y ?y)))
  (modify ?p (prob 0))
  (pop-focus)
)

(defrule guess-to-high-prob (declare (salience 15))
  (status (step ?s) (currently running))
  (moves (guesses ?ng&:(> ?ng 0)))
  ;;seleziona la casella con probabilità più alta tra tutte
  ?p <- (p-cell (x ?x) (y ?y) (prob ?prob1))
  (not (p-cell (x ?x2&:(neq ?x ?x2)) (y ?y2&:(neq ?y ?y2)) (prob ?prob2&:(> ?prob2 ?prob1))))
=>
  (assert (exec (step ?s) (action guess) (x ?x) (y ?y)))
  (modify ?p (prob 0))
  (pop-focus)
)

(defrule solve-when-no-fire-or-guess-left (declare (salience -10))
	(status (step ?s) (currently running))
	(moves (fires ?fs&:(<= ?fs 0)) (guesses ?ng&:(<= ?ng 0)))
=>
	(assert (exec (step ?s) (action solve)))
)
