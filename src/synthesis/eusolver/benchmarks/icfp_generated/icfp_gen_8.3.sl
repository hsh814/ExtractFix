(set-logic BV)

(define-fun shr1 ((x (BitVec 64))) (BitVec 64) (bvlshr x #x0000000000000001))
(define-fun shr4 ((x (BitVec 64))) (BitVec 64) (bvlshr x #x0000000000000004))
(define-fun shr16 ((x (BitVec 64))) (BitVec 64) (bvlshr x #x0000000000000010))
(define-fun shl1 ((x (BitVec 64))) (BitVec 64) (bvshl x #x0000000000000001))
(define-fun if0 ((x (BitVec 64)) (y (BitVec 64)) (z (BitVec 64))) (BitVec 64) (ite (= x #x0000000000000001) y z))

(synth-fun f ( (x (BitVec 64))) (BitVec 64)
(

(Start (BitVec 64) (#x0000000000000000 #x0000000000000001 x (bvnot Start)
                    (shl1 Start)
 		    (shr1 Start)
		    (shr4 Start)
		    (shr16 Start)
		    (bvand Start Start)
		    (bvor Start Start)
		    (bvxor Start Start)
		    (bvadd Start Start)
		    (if0 Start Start Start)
 ))
)
)
(constraint (= (f #xCFBAE81390AFA698) #xFFFFFFFFCFBAE813))
(constraint (= (f #xD084207D0E11E641) #xFFFFFFFFD084207D))
(constraint (= (f #x2695FD2BFA0973DD) #xFFFFFFFF2695FD2B))
(constraint (= (f #x1DB98E96C36AC14C) #xFFFFFFFF1DB98E96))
(constraint (= (f #x93D97B67C0134561) #xFFFFFFFF93D97B67))
(constraint (= (f #x319631563C9378AF) #x19CD39D5386D90EA))
(constraint (= (f #xB0CA4AB4CFF52177) #x09E6B6A966015BD1))
(constraint (= (f #x8849FE48422D5F4F) #x0EF6C036F7BA5416))
(constraint (= (f #x90B3A3A8146F2B73) #x0DE98B8AFD721A91))
(constraint (= (f #x95EFE7D3997EAAA3) #x0D4203058CD02AAB))
(constraint (= (f #x000000000001B238) #xFFFFFFFF00000000))
(constraint (= (f #x000000000001AF24) #xFFFFFFFF00000000))
(constraint (= (f #x00000000000107D1) #xFFFFFFFF00000000))
(constraint (= (f #x000000000001C2E1) #xFFFFFFFF00000000))
(constraint (= (f #x0000000000015DD0) #xFFFFFFFF00000000))
(constraint (= (f #xA424100229285149) #xFFFFFFFF00000000))
(constraint (= (f #x4A84894A88240885) #xFFFFFFFF00000000))
(constraint (= (f #x85524490902A9155) #xFFFFFFFF00000000))
(constraint (= (f #x24A544A4A4485121) #xFFFFFFFF00000000))
(constraint (= (f #x14A490A45044A529) #xFFFFFFFF00000000))
(constraint (= (f #x00000000000152C3) #xFFFFFFFF00000000))
(constraint (= (f #x0000000000012D93) #xFFFFFFFF00000000))
(constraint (= (f #x000000000001BB0B) #xFFFFFFFF00000000))
(constraint (= (f #x00000000000183AF) #xFFFFFFFF00000000))
(constraint (= (f #x0000000000014F8B) #xFFFFFFFF00000000))
(constraint (= (f #x922CAA595A0F05DA) #x0DBA6AB4D4BE1F44))
(constraint (= (f #x888F3A18A2AC2B5E) #x0EEE18BCEBAA7A94))
(constraint (= (f #xCDEF76ACA8776616) #x0642112A6AF1133D))
(constraint (= (f #x5A67867F8134B38E) #x14B30F300FD9698E))
(constraint (= (f #x328BFE6D823E8EB6) #x19AE80324FB82E29))
(constraint (= (f #x0000000000015021) #xFFFFFFFF00000000))
(constraint (= (f #x0000000000010A85) #xFFFFFFFF00000000))
(constraint (= (f #x0000000000014495) #xFFFFFFFF00000000))
(constraint (= (f #x0000000000015451) #xFFFFFFFF00000000))
(constraint (= (f #x0000000000012495) #xFFFFFFFF00000000))
(constraint (= (f #x0000000000000001) #xFFFFFFFF00000000))
(constraint (= (f #x0000000000016F96) #x1FFFFFFFFFFFD20D))
(constraint (= (f #x0000000000017C06) #x1FFFFFFFFFFFD07F))
(constraint (= (f #x0000000000014BDE) #x1FFFFFFFFFFFD684))
(constraint (= (f #x000000000001B426) #x1FFFFFFFFFFFC97B))
(constraint (= (f #x0000000000015A0E) #x1FFFFFFFFFFFD4BE))
(constraint (= (f #xFFFF0000FFFF0002) #x1FFFFFFFFFFFFFFF))
(check-synth)
