[tool-version] Z3 4.12.5
[mk-app] #1 true
[mk-app] #2 false
[mk-app] #1 true
[mk-app] #2 false
[mk-app] #3 pi
[mk-app] #4 euler
[mk-var] datatype#0 0
[mk-var] datatype#1 1
[mk-app] datatype#2 insert datatype#0 datatype#1
[mk-app] datatype#3 pattern datatype#2
[mk-app] datatype#4 head datatype#2
[mk-app] datatype#5 = datatype#0 datatype#4
[mk-quant] datatype#6 constructor_accessor_axiom 2 datatype#3 datatype#5
[attach-var-names] datatype#6 (;k!0) (;List)
[mk-app] datatype#7 tail datatype#2
[mk-app] datatype#8 = datatype#1 datatype#7
[mk-quant] datatype#9 constructor_accessor_axiom 2 datatype#3 datatype#8
[attach-var-names] datatype#9 (;k!0) (;List)
[mk-app] #5 bv
[attach-meaning] #5 bv #b1
[mk-app] #6 bv
[attach-meaning] #6 bv #b0
[attach-meaning] #5 bv #b1
[attach-meaning] #6 bv #b0
[attach-meaning] #6 bv #b0
[mk-var] #7 0
[mk-var] #8 1
[mk-var] #9 2
[mk-var] #10 3
[mk-var] #11 4
[mk-var] #12 5
[mk-var] #13 6
[mk-var] #14 7
[mk-var] #15 8
[mk-var] #16 9
[mk-var] #17 10
[mk-var] #18 11
[mk-var] #19 12
[mk-var] #20 13
[mk-var] #21 14
[mk-app] #22 + #15 #13
[attach-enode] #1 0
[attach-enode] #2 0
[mk-app] #23 fuel_defaults
[mk-var] #24 0
[mk-app] #25 fuel_bool #24
[mk-app] #26 fuel_bool_default #24
[mk-app] #27 = #25 #26
[mk-app] #28 pattern #25
[mk-quant] #29 prelude_fuel_defaults 1 #28 #27
[attach-var-names] #29 (|id| ; |FuelId|)
[mk-app] #30 => #23 #29
[mk-app] #31 not #23
[mk-app] #32 or #31 #29
[inst-discovered] theory-solving 0 basic# ; #30
[mk-app] #33 = #30 #32
[instance] 0 #33
[attach-enode] #33 0
[end-of-instance]
[mk-var] #33 1
[mk-var] #34 0
[mk-app] #35 mut_ref_update_current% #33 #34
[mk-app] #36 mut_ref_current% #35
[mk-app] #37 = #36 #34
[mk-app] #38 pattern #35
[mk-quant] #39 prelude_mut_ref_update_current_current 2 #38 #37
[attach-var-names] #39 (|arg| ; |Poly|) (|m| ; |Poly|)
[mk-app] #40 mut_ref_future% #35
[mk-app] #41 mut_ref_future% #33
[mk-app] #42 = #40 #41
[mk-quant] #43 prelude_mut_ref_update_current_future 2 #38 #42
[attach-var-names] #43 (|arg| ; |Poly|) (|m| ; |Poly|)
[mk-var] #44 2
[mk-var] #45 1
[mk-var] #46 0
[mk-app] #47 MUTREF #45 #46
[mk-app] #48 has_type #44 #47
[mk-app] #49 mut_ref_current% #44
[mk-app] #50 has_type #49 #46
[mk-app] #51 => #48 #50
[mk-app] #52 pattern #48 #49
[mk-quant] #53 prelude_mut_ref_current_has_type 3 #52 #51
[attach-var-names] #53 (|t| ; |Type|) (|d| ; |Dcr|) (|m| ; |Poly|)
[mk-app] #54 not #48
[mk-app] #55 or #54 #50
[inst-discovered] theory-solving 0 basic# ; #51
[mk-app] #56 = #51 #55
[instance] 0 #56
[attach-enode] #56 0
[end-of-instance]
[mk-quant] #56 prelude_mut_ref_current_has_type 3 #52 #55
[attach-var-names] #56 (|t| ; |Type|) (|d| ; |Dcr|) (|m| ; |Poly|)
[mk-app] #57 mut_ref_future% #44
[mk-app] #58 has_type #57 #46
[mk-app] #59 => #48 #58
[mk-app] #60 pattern #48 #57
[mk-quant] #61 prelude_mut_ref_current_has_type 3 #60 #59
[attach-var-names] #61 (|t| ; |Type|) (|d| ; |Dcr|) (|m| ; |Poly|)
[mk-app] #62 or #54 #58
[inst-discovered] theory-solving 0 basic# ; #59
[mk-app] #63 = #59 #62
[instance] 0 #63
[attach-enode] #63 0
[end-of-instance]
[mk-quant] #63 prelude_mut_ref_current_has_type 3 #60 #62
[attach-var-names] #63 (|t| ; |Type|) (|d| ; |Dcr|) (|m| ; |Poly|)
[mk-var] #64 3
[mk-var] #65 2
[mk-var] #66 1
[mk-app] #67 MUTREF #65 #66
[mk-app] #68 has_type #64 #67
[mk-app] #69 has_type #34 #66
[mk-app] #70 and #68 #69
[mk-app] #71 mut_ref_update_current% #64 #34
[mk-app] #72 has_type #71 #67
[mk-app] #73 => #70 #72
[mk-app] #74 pattern #68 #71
[mk-quant] #75 prelude_mut_ref_update_has_type 4 #74 #73
[attach-var-names] #75 (|arg| ; |Poly|) (|t| ; |Type|) (|d| ; |Dcr|) (|m| ; |Poly|)
[mk-app] #76 not #70
[mk-app] #77 or #76 #72
[inst-discovered] theory-solving 0 basic# ; #73
[mk-app] #78 = #73 #77
[instance] 0 #78
[attach-enode] #78 0
[end-of-instance]
[mk-quant] #78 prelude_mut_ref_update_has_type 4 #74 #77
[attach-var-names] #78 (|arg| ; |Poly|) (|t| ; |Type|) (|d| ; |Dcr|) (|m| ; |Poly|)
[mk-var] #79 0
[mk-app] #80 sized #79
[mk-app] #81 DST #79
[mk-app] #82 sized #81
[mk-app] #83 => #80 #82
[mk-app] #84 pattern #82
[mk-quant] #85 prelude_sized_decorate_struct_inherit 1 #84 #83
[attach-var-names] #85 (|d| ; |Dcr|)
[mk-app] #86 not #80
[mk-app] #87 or #86 #82
[inst-discovered] theory-solving 0 basic# ; #83
[mk-app] #88 = #83 #87
[instance] 0 #88
[attach-enode] #88 0
[end-of-instance]
[mk-quant] #88 prelude_sized_decorate_struct_inherit 1 #84 #87
[attach-var-names] #88 (|d| ; |Dcr|)
[mk-app] #89 REF #79
[mk-app] #90 sized #89
[mk-app] #91 pattern #90
[mk-quant] #92 prelude_sized_decorate_ref 1 #91 #90
[attach-var-names] #92 (|d| ; |Dcr|)
[mk-app] #93 BOX #65 #66 #79
[mk-app] #94 sized #93
[mk-app] #95 pattern #94
[mk-quant] #96 prelude_sized_decorate_box 3 #95 #94
[attach-var-names] #96 (|d2| ; |Dcr|) (|t| ; |Type|) (|d| ; |Dcr|)
[mk-app] #97 RC #65 #66 #79
[mk-app] #98 sized #97
[mk-app] #99 pattern #98
[mk-quant] #100 prelude_sized_decorate_rc 3 #99 #98
[attach-var-names] #100 (|d2| ; |Dcr|) (|t| ; |Type|) (|d| ; |Dcr|)
[mk-app] #101 ARC #65 #66 #79
[mk-app] #102 sized #101
[mk-app] #103 pattern #102
[mk-quant] #104 prelude_sized_decorate_arc 3 #103 #102
[attach-var-names] #104 (|d2| ; |Dcr|) (|t| ; |Type|) (|d| ; |Dcr|)
[mk-app] #105 GHOST #79
[mk-app] #106 sized #105
[mk-app] #107 pattern #106
[mk-quant] #108 prelude_sized_decorate_ghost 1 #107 #106
[attach-var-names] #108 (|d| ; |Dcr|)
[mk-app] #109 TRACKED #79
[mk-app] #110 sized #109
[mk-app] #111 pattern #110
[mk-quant] #112 prelude_sized_decorate_tracked 1 #111 #110
[attach-var-names] #112 (|d| ; |Dcr|)
[mk-app] #113 NEVER #79
[mk-app] #114 sized #113
[mk-app] #115 pattern #114
[mk-quant] #116 prelude_sized_decorate_never 1 #115 #114
[attach-var-names] #116 (|d| ; |Dcr|)
[mk-app] #117 CONST_PTR #79
[mk-app] #118 sized #117
[mk-app] #119 pattern #118
[mk-quant] #120 prelude_sized_decorate_const_ptr 1 #119 #118
[attach-var-names] #120 (|d| ; |Dcr|)
[mk-app] #121 $
[mk-app] #122 sized #121
[mk-var] #123 0
[mk-app] #124 CONST_INT #123
[mk-app] #125 const_int #124
[mk-app] #126 = #123 #125
[mk-app] #127 pattern #124
[mk-quant] #128 prelude_type_id_const_int 1 #127 #126
[attach-var-names] #128 (|i| ; |Int|)
[mk-var] #129 0
[mk-app] #130 CONST_BOOL #129
[mk-app] #131 const_bool #130
[mk-app] #132 = #129 #131
[mk-app] #133 pattern #130
[mk-quant] #134 prelude_type_id_const_bool 1 #133 #132
[attach-var-names] #134 (|b| ; |Bool|)
[mk-app] #135 B #129
[mk-app] #136 BOOL
[mk-app] #137 has_type #135 #136
[mk-app] #138 pattern #137
[mk-quant] #139 prelude_has_type_bool 1 #138 #137
[attach-var-names] #139 (|b| ; |Bool|)
[mk-app] #140 R #7
[mk-app] #141 REAL
[mk-app] #142 has_type #140 #141
[mk-app] #143 pattern #142
[mk-quant] #144 prelude_has_type_real 1 #143 #142
[attach-var-names] #144 (|r| ; |Real|)
[mk-app] #145 as_type #33 #46
[mk-app] #146 has_type #145 #46
[mk-app] #147 has_type #33 #46
[mk-app] #148 = #33 #145
[mk-app] #149 => #147 #148
[mk-app] #150 and #146 #149
[mk-app] #151 pattern #145
[mk-quant] #152 prelude_as_type 2 #151 #150
[attach-var-names] #152 (|t| ; |Type|) (|x| ; |Poly|)
[mk-app] #153 not #147
[mk-app] #154 or #153 #148
[inst-discovered] theory-solving 0 basic# ; #149
[mk-app] #155 = #149 #154
[instance] 0 #155
[attach-enode] #155 0
[end-of-instance]
[mk-app] #155 and #146 #154
[mk-quant] #156 prelude_as_type 2 #151 #155
[attach-var-names] #156 (|t| ; |Type|) (|x| ; |Poly|)
[mk-var] #157 0
[mk-app] #158 mk_fun #157
[mk-app] #159 = #158 #157
[mk-app] #160 pattern #158
[mk-quant] #161 prelude_mk_fun 1 #160 #159
[attach-var-names] #161 (|x| ; |%%Function%%|)
[mk-app] #162 %B #135
[mk-app] #163 = #129 #162
[mk-app] #164 pattern #135
[mk-quant] #165 prelude_unbox_box_bool 1 #164 #163
[attach-var-names] #165 (|x| ; |Bool|)
[mk-app] #166 I #123
[mk-app] #167 %I #166
[mk-app] #168 = #123 #167
[mk-app] #169 pattern #166
[mk-quant] #170 prelude_unbox_box_int 1 #169 #168
[attach-var-names] #170 (|x| ; |Int|)
[mk-app] #171 %R #140
[mk-app] #172 = #7 #171
[mk-app] #173 pattern #140
[mk-quant] #174 prelude_unbox_box_real 1 #173 #172
[attach-var-names] #174 (|x| ; |Real|)
[mk-app] #175 has_type #34 #136
[mk-app] #176 %B #34
[mk-app] #177 B #176
[mk-app] #178 = #34 #177
[mk-app] #179 => #175 #178
[mk-app] #180 pattern #175
[mk-quant] #181 prelude_box_unbox_bool 1 #180 #179
[attach-var-names] #181 (|x| ; |Poly|)
[mk-app] #182 not #175
[mk-app] #183 or #182 #178
[inst-discovered] theory-solving 0 basic# ; #179
[mk-app] #184 = #179 #183
[instance] 0 #184
[attach-enode] #184 0
[end-of-instance]
[mk-quant] #184 prelude_box_unbox_bool 1 #180 #183
[attach-var-names] #184 (|x| ; |Poly|)
[mk-app] #185 INT
[mk-app] #186 has_type #34 #185
[mk-app] #187 %I #34
[mk-app] #188 I #187
[mk-app] #189 = #34 #188
[mk-app] #190 => #186 #189
[mk-app] #191 pattern #186
[mk-quant] #192 prelude_box_unbox_int 1 #191 #190
[attach-var-names] #192 (|x| ; |Poly|)
[mk-app] #193 not #186
[mk-app] #194 or #193 #189
[inst-discovered] theory-solving 0 basic# ; #190
[mk-app] #195 = #190 #194
[instance] 0 #195
[attach-enode] #195 0
[end-of-instance]
[mk-quant] #195 prelude_box_unbox_int 1 #191 #194
[attach-var-names] #195 (|x| ; |Poly|)
[mk-app] #196 NAT
[mk-app] #197 has_type #34 #196
[mk-app] #198 => #197 #189
[mk-app] #199 pattern #197
[mk-quant] #200 prelude_box_unbox_nat 1 #199 #198
[attach-var-names] #200 (|x| ; |Poly|)
[mk-app] #201 not #197
[mk-app] #202 or #201 #189
[inst-discovered] theory-solving 0 basic# ; #198
[mk-app] #203 = #198 #202
[instance] 0 #203
[attach-enode] #203 0
[end-of-instance]
[mk-quant] #203 prelude_box_unbox_nat 1 #199 #202
[attach-var-names] #203 (|x| ; |Poly|)
[mk-app] #204 USIZE
[mk-app] #205 has_type #34 #204
[mk-app] #206 => #205 #189
[mk-app] #207 pattern #205
[mk-quant] #208 prelude_box_unbox_usize 1 #207 #206
[attach-var-names] #208 (|x| ; |Poly|)
[mk-app] #209 not #205
[mk-app] #210 or #209 #189
[inst-discovered] theory-solving 0 basic# ; #206
[mk-app] #211 = #206 #210
[instance] 0 #211
[attach-enode] #211 0
[end-of-instance]
[mk-quant] #211 prelude_box_unbox_usize 1 #207 #210
[attach-var-names] #211 (|x| ; |Poly|)
[mk-app] #212 ISIZE
[mk-app] #213 has_type #34 #212
[mk-app] #214 => #213 #189
[mk-app] #215 pattern #213
[mk-quant] #216 prelude_box_unbox_isize 1 #215 #214
[attach-var-names] #216 (|x| ; |Poly|)
[mk-app] #217 not #213
[mk-app] #218 or #217 #189
[inst-discovered] theory-solving 0 basic# ; #214
[mk-app] #219 = #214 #218
[instance] 0 #219
[attach-enode] #219 0
[end-of-instance]
[mk-quant] #219 prelude_box_unbox_isize 1 #215 #218
[attach-var-names] #219 (|x| ; |Poly|)
[mk-var] #220 1
[mk-app] #221 UINT #220
[mk-app] #222 has_type #34 #221
[mk-app] #223 => #222 #189
[mk-app] #224 pattern #222
[mk-quant] #225 prelude_box_unbox_uint 2 #224 #223
[attach-var-names] #225 (|x| ; |Poly|) (|bits| ; |Int|)
[mk-app] #226 not #222
[mk-app] #227 or #226 #189
[inst-discovered] theory-solving 0 basic# ; #223
[mk-app] #228 = #223 #227
[instance] 0 #228
[attach-enode] #228 0
[end-of-instance]
[mk-quant] #228 prelude_box_unbox_uint 2 #224 #227
[attach-var-names] #228 (|x| ; |Poly|) (|bits| ; |Int|)
[mk-app] #229 SINT #220
[mk-app] #230 has_type #34 #229
[mk-app] #231 => #230 #189
[mk-app] #232 pattern #230
[mk-quant] #233 prelude_box_unbox_sint 2 #232 #231
[attach-var-names] #233 (|x| ; |Poly|) (|bits| ; |Int|)
[mk-app] #234 not #230
[mk-app] #235 or #234 #189
[inst-discovered] theory-solving 0 basic# ; #231
[mk-app] #236 = #231 #235
[instance] 0 #236
[attach-enode] #236 0
[end-of-instance]
[mk-quant] #236 prelude_box_unbox_sint 2 #232 #235
[attach-var-names] #236 (|x| ; |Poly|) (|bits| ; |Int|)
[mk-app] #237 FLOAT #220
[mk-app] #238 has_type #34 #237
[mk-app] #239 => #238 #189
[mk-app] #240 pattern #238
[mk-quant] #241 prelude_box_unbox_sint 2 #240 #239
[attach-var-names] #241 (|x| ; |Poly|) (|bits| ; |Int|)
[mk-app] #242 not #238
[mk-app] #243 or #242 #189
[inst-discovered] theory-solving 0 basic# ; #239
[mk-app] #244 = #239 #243
[instance] 0 #244
[attach-enode] #244 0
[end-of-instance]
[mk-quant] #244 prelude_box_unbox_sint 2 #240 #243
[attach-var-names] #244 (|x| ; |Poly|) (|bits| ; |Int|)
[mk-app] #245 CHAR
[mk-app] #246 has_type #34 #245
[mk-app] #247 => #246 #189
[mk-app] #248 pattern #246
[mk-quant] #249 prelude_box_unbox_char 1 #248 #247
[attach-var-names] #249 (|x| ; |Poly|)
[mk-app] #250 not #246
[mk-app] #251 or #250 #189
[inst-discovered] theory-solving 0 basic# ; #247
[mk-app] #252 = #247 #251
[instance] 0 #252
[attach-enode] #252 0
[end-of-instance]
[mk-quant] #252 prelude_box_unbox_char 1 #248 #251
[attach-var-names] #252 (|x| ; |Poly|)
[mk-app] #253 has_type #34 #141
[mk-app] #254 %R #34
[mk-app] #255 R #254
[mk-app] #256 = #34 #255
[mk-app] #257 => #253 #256
[mk-app] #258 pattern #253
[mk-quant] #259 prelude_box_unbox_real 1 #258 #257
[attach-var-names] #259 (|x| ; |Poly|)
[mk-app] #260 not #253
[mk-app] #261 or #260 #256
[inst-discovered] theory-solving 0 basic# ; #257
[mk-app] #262 = #257 #261
[instance] 0 #262
[attach-enode] #262 0
[end-of-instance]
[mk-quant] #262 prelude_box_unbox_real 1 #258 #261
[attach-var-names] #262 (|x| ; |Poly|)
[mk-var] #263 3
[mk-var] #264 2
[mk-app] #265 = #33 #34
[mk-app] #266 ext_eq #263 #264 #33 #34
[mk-app] #267 = #265 #266
[mk-app] #268 pattern #266
[mk-quant] #269 prelude_ext_eq 4 #268 #267
[attach-var-names] #269 (|y| ; |Poly|) (|x| ; |Poly|) (|t| ; |Type|) (|deep| ; |Bool|)
[mk-app] #270 SZ
[mk-app] #271 Int
[attach-meaning] #271 arith 32
[mk-app] #272 = #270 #271
[mk-app] #273 Int
[attach-meaning] #273 arith 64
[mk-app] #274 = #270 #273
[mk-app] #275 or #272 #274
[mk-app] #276 Int
[attach-meaning] #276 arith 8
[mk-app] #277 uHi #276
[mk-app] #278 Int
[attach-meaning] #278 arith 256
[mk-app] #279 = #277 #278
[mk-app] #280 Int
[attach-meaning] #280 arith 16
[mk-app] #281 uHi #280
[mk-app] #282 Int
[attach-meaning] #282 arith 65536
[mk-app] #283 = #281 #282
[attach-meaning] #271 arith 32
[mk-app] #284 uHi #271
[mk-app] #285 Int
[attach-meaning] #285 arith 4294967296
[mk-app] #286 = #284 #285
[attach-meaning] #273 arith 64
[mk-app] #287 uHi #273
[mk-app] #288 Int
[attach-meaning] #288 arith 18446744073709551616
[mk-app] #289 = #287 #288
[mk-app] #290 Int
[attach-meaning] #290 arith 128
[mk-app] #291 uHi #290
[mk-app] #292 Int
[attach-meaning] #292 arith 1
[mk-app] #293 Int
[attach-meaning] #293 arith 340282366920938463463374607431768211455
[mk-app] #294 + #292 #293
[mk-app] #295 = #291 #294
[mk-app] #296 Int
[attach-meaning] #296 arith 340282366920938463463374607431768211456
[inst-discovered] theory-solving 0 arith# ; #294
[mk-app] #297 = #294 #296
[instance] 0 #297
[attach-enode] #297 0
[end-of-instance]
[mk-app] #297 = #291 #296
[mk-app] #298 iLo #276
[attach-meaning] #290 arith 128
[mk-app] #299 - #290
[mk-app] #300 = #298 #299
[mk-app] #301 Int
[attach-meaning] #301 arith (- 128)
[inst-discovered] theory-solving 0 arith# ; #299
[mk-app] #302 = #299 #301
[instance] 0 #302
[attach-enode] #302 0
[end-of-instance]
[mk-app] #302 = #298 #301
[attach-meaning] #280 arith 16
[mk-app] #303 iLo #280
[mk-app] #304 Int
[attach-meaning] #304 arith 32768
[mk-app] #305 - #304
[mk-app] #306 = #303 #305
[mk-app] #307 Int
[attach-meaning] #307 arith (- 32768)
[inst-discovered] theory-solving 0 arith# ; #305
[mk-app] #308 = #305 #307
[instance] 0 #308
[attach-enode] #308 0
[end-of-instance]
[mk-app] #308 = #303 #307
[attach-meaning] #271 arith 32
[mk-app] #309 iLo #271
[mk-app] #310 Int
[attach-meaning] #310 arith 2147483648
[mk-app] #311 - #310
[mk-app] #312 = #309 #311
[mk-app] #313 Int
[attach-meaning] #313 arith (- 2147483648)
[inst-discovered] theory-solving 0 arith# ; #311
[mk-app] #314 = #311 #313
[instance] 0 #314
[attach-enode] #314 0
[end-of-instance]
[mk-app] #314 = #309 #313
[attach-meaning] #273 arith 64
[mk-app] #315 iLo #273
[mk-app] #316 Int
[attach-meaning] #316 arith 9223372036854775808
[mk-app] #317 - #316
[mk-app] #318 = #315 #317
[mk-app] #319 Int
[attach-meaning] #319 arith (- 9223372036854775808)
[inst-discovered] theory-solving 0 arith# ; #317
[mk-app] #320 = #317 #319
[instance] 0 #320
[attach-enode] #320 0
[end-of-instance]
[mk-app] #320 = #315 #319
[attach-meaning] #290 arith 128
[mk-app] #321 iLo #290
[mk-app] #322 Int
[attach-meaning] #322 arith 170141183460469231731687303715884105728
[mk-app] #323 - #322
[mk-app] #324 = #321 #323
[mk-app] #325 Int
[attach-meaning] #325 arith (- 170141183460469231731687303715884105728)
[inst-discovered] theory-solving 0 arith# ; #323
[mk-app] #326 = #323 #325
[instance] 0 #326
[attach-enode] #326 0
[end-of-instance]
[mk-app] #326 = #321 #325
[mk-app] #327 iHi #276
[attach-meaning] #290 arith 128
[mk-app] #328 = #327 #290
[attach-meaning] #280 arith 16
[mk-app] #329 iHi #280
[attach-meaning] #304 arith 32768
[mk-app] #330 = #329 #304
[attach-meaning] #271 arith 32
[mk-app] #331 iHi #271
[attach-meaning] #310 arith 2147483648
[mk-app] #332 = #331 #310
[attach-meaning] #273 arith 64
[mk-app] #333 iHi #273
[attach-meaning] #316 arith 9223372036854775808
[mk-app] #334 = #333 #316
[attach-meaning] #290 arith 128
[mk-app] #335 iHi #290
[attach-meaning] #322 arith 170141183460469231731687303715884105728
[mk-app] #336 = #335 #322
[mk-app] #337 Int
[attach-meaning] #337 arith 0
[mk-app] #338 nClip #123
[mk-app] #339 <= #337 #338
[mk-app] #340 <= #337 #123
[mk-app] #341 = #123 #338
[mk-app] #342 => #340 #341
[mk-app] #343 and #339 #342
[mk-app] #344 pattern #338
[mk-quant] #345 prelude_nat_clip 1 #344 #343
[attach-var-names] #345 (|i| ; |Int|)
[mk-app] #346 Int
[attach-meaning] #346 arith (- 1)
[mk-app] #347 * #346 #338
[mk-app] #348 >= #338 #337
[inst-discovered] theory-solving 0 arith# ; #339
[mk-app] #346 = #339 #348
[instance] 0 #346
[attach-enode] #346 0
[end-of-instance]
[mk-app] #346 Int
[attach-meaning] #346 arith (- 1)
[mk-app] #347 * #346 #123
[mk-app] #349 >= #123 #337
[inst-discovered] theory-solving 0 arith# ; #340
[mk-app] #346 = #340 #349
[instance] 0 #346
[attach-enode] #346 0
[end-of-instance]
[mk-app] #346 not #349
[mk-app] #347 or #346 #341
[mk-app] #350 => #349 #341
[inst-discovered] theory-solving 0 basic# ; #350
[mk-app] #351 = #350 #347
[instance] 0 #351
[attach-enode] #351 0
[end-of-instance]
[mk-app] #350 and #348 #347
[mk-quant] #351 prelude_nat_clip 1 #344 #350
[attach-var-names] #351 (|i| ; |Int|)
[mk-app] #352 uClip #220 #123
[mk-app] #353 <= #337 #352
[mk-app] #354 uHi #220
[mk-app] #355 < #352 #354
[mk-app] #356 < #123 #354
[mk-app] #357 and #340 #356
[mk-app] #358 = #123 #352
[mk-app] #359 => #357 #358
[mk-app] #360 and #353 #355 #359
[mk-app] #361 pattern #352
[mk-quant] #362 prelude_u_clip 2 #361 #360
[attach-var-names] #362 (|i| ; |Int|) (|bits| ; |Int|)
[mk-app] #363 Int
[attach-meaning] #363 arith (- 1)
[mk-app] #364 * #363 #352
[mk-app] #365 >= #352 #337
[inst-discovered] theory-solving 0 arith# ; #353
[mk-app] #363 = #353 #365
[instance] 0 #363
[attach-enode] #363 0
[end-of-instance]
[mk-app] #363 <= #354 #352
[mk-app] #364 not #363
[inst-discovered] theory-solving 0 arith# ; #355
[mk-app] #366 = #355 #364
[instance] 0 #366
[attach-enode] #366 0
[end-of-instance]
[mk-app] #366 Int
[attach-meaning] #366 arith (- 1)
[mk-app] #367 * #366 #352
[mk-app] #368 + #367 #354
[attach-meaning] #366 arith (- 1)
[mk-app] #369 * #366 #354
[mk-app] #370 + #352 #369
[mk-app] #367 >= #370 #337
[inst-discovered] theory-solving 0 arith# ; #363
[mk-app] #368 = #363 #367
[instance] 0 #368
[attach-enode] #368 0
[end-of-instance]
[mk-app] #368 not #367
[attach-meaning] #366 arith (- 1)
[mk-app] #371 * #366 #123
[inst-discovered] theory-solving 0 arith# ; #340
[mk-app] #371 = #340 #349
[instance] 0 #371
[attach-enode] #371 0
[end-of-instance]
[mk-app] #371 <= #354 #123
[mk-app] #372 not #371
[inst-discovered] theory-solving 0 arith# ; #356
[mk-app] #373 = #356 #372
[instance] 0 #373
[attach-enode] #373 0
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #373 * #366 #123
[mk-app] #374 + #373 #354
[attach-meaning] #366 arith (- 1)
[mk-app] #375 + #123 #369
[mk-app] #373 >= #375 #337
[inst-discovered] theory-solving 0 arith# ; #371
[mk-app] #374 = #371 #373
[instance] 0 #374
[attach-enode] #374 0
[end-of-instance]
[mk-app] #374 not #373
[mk-app] #376 and #349 #374
[mk-app] #377 not #376
[mk-app] #378 or #377 #358
[mk-app] #379 => #376 #358
[inst-discovered] theory-solving 0 basic# ; #379
[mk-app] #380 = #379 #378
[instance] 0 #380
[attach-enode] #380 0
[end-of-instance]
[mk-app] #379 and #365 #368 #378
[mk-quant] #380 prelude_u_clip 2 #361 #379
[attach-var-names] #380 (|i| ; |Int|) (|bits| ; |Int|)
[mk-app] #363 iLo #220
[mk-app] #364 iClip #220 #123
[mk-app] #371 <= #363 #364
[mk-app] #372 iHi #220
[mk-app] #381 < #364 #372
[mk-app] #382 <= #363 #123
[mk-app] #383 < #123 #372
[mk-app] #384 and #382 #383
[mk-app] #385 = #123 #364
[mk-app] #386 => #384 #385
[mk-app] #387 and #371 #381 #386
[mk-app] #388 pattern #364
[mk-quant] #389 prelude_i_clip 2 #388 #387
[attach-var-names] #389 (|i| ; |Int|) (|bits| ; |Int|)
[attach-meaning] #366 arith (- 1)
[mk-app] #390 * #366 #364
[mk-app] #391 + #363 #390
[mk-app] #392 <= #391 #337
[inst-discovered] theory-solving 0 arith# ; #371
[mk-app] #393 = #371 #392
[instance] 0 #393
[attach-enode] #393 0
[end-of-instance]
[mk-app] #393 <= #372 #364
[mk-app] #394 not #393
[inst-discovered] theory-solving 0 arith# ; #381
[mk-app] #395 = #381 #394
[instance] 0 #395
[attach-enode] #395 0
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #395 + #390 #372
[attach-meaning] #366 arith (- 1)
[mk-app] #396 * #366 #372
[mk-app] #397 + #364 #396
[mk-app] #395 >= #397 #337
[inst-discovered] theory-solving 0 arith# ; #393
[mk-app] #398 = #393 #395
[instance] 0 #398
[attach-enode] #398 0
[end-of-instance]
[mk-app] #398 not #395
[attach-meaning] #366 arith (- 1)
[mk-app] #399 * #366 #123
[mk-app] #400 + #399 #363
[attach-meaning] #366 arith (- 1)
[mk-app] #401 * #366 #363
[mk-app] #402 + #123 #401
[mk-app] #399 >= #402 #337
[inst-discovered] theory-solving 0 arith# ; #382
[mk-app] #400 = #382 #399
[instance] 0 #400
[attach-enode] #400 0
[end-of-instance]
[mk-app] #400 <= #372 #123
[mk-app] #403 not #400
[inst-discovered] theory-solving 0 arith# ; #383
[mk-app] #404 = #383 #403
[instance] 0 #404
[attach-enode] #404 0
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #404 * #366 #123
[mk-app] #405 + #404 #372
[attach-meaning] #366 arith (- 1)
[mk-app] #406 + #123 #396
[mk-app] #404 >= #406 #337
[inst-discovered] theory-solving 0 arith# ; #400
[mk-app] #405 = #400 #404
[instance] 0 #405
[attach-enode] #405 0
[end-of-instance]
[mk-app] #405 not #404
[mk-app] #407 and #399 #405
[mk-app] #408 not #407
[mk-app] #409 or #408 #385
[mk-app] #410 => #407 #385
[inst-discovered] theory-solving 0 basic# ; #410
[mk-app] #411 = #410 #409
[instance] 0 #411
[attach-enode] #411 0
[end-of-instance]
[mk-app] #410 and #392 #398 #409
[mk-quant] #411 prelude_i_clip 2 #388 #410
[attach-var-names] #411 (|i| ; |Int|) (|bits| ; |Int|)
[mk-app] #400 charClip #123
[mk-app] #403 <= #337 #400
[mk-app] #393 Int
[attach-meaning] #393 arith 55295
[mk-app] #394 <= #400 #393
[mk-app] #412 and #403 #394
[mk-app] #413 Int
[attach-meaning] #413 arith 57344
[mk-app] #414 <= #413 #400
[mk-app] #415 Int
[attach-meaning] #415 arith 1114111
[mk-app] #416 <= #400 #415
[mk-app] #417 and #414 #416
[mk-app] #418 or #412 #417
[attach-meaning] #393 arith 55295
[mk-app] #419 <= #123 #393
[mk-app] #420 and #340 #419
[attach-meaning] #413 arith 57344
[mk-app] #421 <= #413 #123
[attach-meaning] #415 arith 1114111
[mk-app] #422 <= #123 #415
[mk-app] #423 and #421 #422
[mk-app] #424 or #420 #423
[mk-app] #425 = #123 #400
[mk-app] #426 => #424 #425
[mk-app] #427 and #418 #426
[mk-app] #428 pattern #400
[mk-quant] #429 prelude_char_clip 1 #428 #427
[attach-var-names] #429 (|i| ; |Int|)
[attach-meaning] #366 arith (- 1)
[mk-app] #430 * #366 #400
[mk-app] #431 >= #400 #337
[inst-discovered] theory-solving 0 arith# ; #403
[mk-app] #430 = #403 #431
[instance] 0 #430
[attach-enode] #430 0
[end-of-instance]
[mk-app] #430 and #431 #394
[attach-meaning] #366 arith (- 1)
[mk-app] #432 * #366 #400
[mk-app] #433 Int
[attach-meaning] #433 arith (- 57344)
[attach-meaning] #413 arith 57344
[mk-app] #434 >= #400 #413
[inst-discovered] theory-solving 0 arith# ; #414
[mk-app] #432 = #414 #434
[instance] 0 #432
[attach-enode] #432 0
[end-of-instance]
[mk-app] #432 and #434 #416
[mk-app] #433 or #430 #432
[attach-meaning] #366 arith (- 1)
[mk-app] #435 * #366 #123
[inst-discovered] theory-solving 0 arith# ; #340
[mk-app] #435 = #340 #349
[instance] 0 #435
[attach-enode] #435 0
[end-of-instance]
[mk-app] #435 and #349 #419
[attach-meaning] #366 arith (- 1)
[mk-app] #436 * #366 #123
[mk-app] #437 Int
[attach-meaning] #437 arith (- 57344)
[attach-meaning] #413 arith 57344
[mk-app] #438 >= #123 #413
[inst-discovered] theory-solving 0 arith# ; #421
[mk-app] #436 = #421 #438
[instance] 0 #436
[attach-enode] #436 0
[end-of-instance]
[mk-app] #436 and #438 #422
[mk-app] #437 or #435 #436
[mk-app] #439 not #437
[mk-app] #440 or #439 #425
[mk-app] #441 => #437 #425
[inst-discovered] theory-solving 0 basic# ; #441
[mk-app] #442 = #441 #440
[instance] 0 #442
[attach-enode] #442 0
[end-of-instance]
[mk-app] #441 and #433 #440
[mk-quant] #442 prelude_char_clip 1 #428 #441
[attach-var-names] #442 (|i| ; |Int|)
[mk-app] #443 uInv #220 #123
[mk-app] #444 = #443 #357
[mk-app] #445 pattern #443
[mk-quant] #446 prelude_u_inv 2 #445 #444
[attach-var-names] #446 (|i| ; |Int|) (|bits| ; |Int|)
[attach-meaning] #366 arith (- 1)
[mk-app] #447 * #366 #123
[inst-discovered] theory-solving 0 arith# ; #340
[mk-app] #447 = #340 #349
[instance] 0 #447
[attach-enode] #447 0
[end-of-instance]
[mk-app] #447 <= #354 #123
[mk-app] #448 not #447
[inst-discovered] theory-solving 0 arith# ; #356
[mk-app] #449 = #356 #448
[instance] 0 #449
[attach-enode] #449 0
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #449 * #366 #123
[mk-app] #450 + #449 #354
[attach-meaning] #366 arith (- 1)
[inst-discovered] theory-solving 0 arith# ; #447
[mk-app] #449 = #447 #373
[instance] 0 #449
[attach-enode] #449 0
[end-of-instance]
[mk-app] #449 = #443 #376
[mk-quant] #450 prelude_u_inv 2 #445 #449
[attach-var-names] #450 (|i| ; |Int|) (|bits| ; |Int|)
[mk-app] #447 iInv #220 #123
[mk-app] #448 = #447 #384
[mk-app] #451 pattern #447
[mk-quant] #452 prelude_i_inv 2 #451 #448
[attach-var-names] #452 (|i| ; |Int|) (|bits| ; |Int|)
[attach-meaning] #366 arith (- 1)
[mk-app] #453 * #366 #123
[mk-app] #454 + #453 #363
[attach-meaning] #366 arith (- 1)
[inst-discovered] theory-solving 0 arith# ; #382
[mk-app] #453 = #382 #399
[instance] 0 #453
[attach-enode] #453 0
[end-of-instance]
[mk-app] #453 <= #372 #123
[mk-app] #454 not #453
[inst-discovered] theory-solving 0 arith# ; #383
[mk-app] #455 = #383 #454
[instance] 0 #455
[attach-enode] #455 0
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #455 * #366 #123
[mk-app] #456 + #455 #372
[attach-meaning] #366 arith (- 1)
[inst-discovered] theory-solving 0 arith# ; #453
[mk-app] #455 = #453 #404
[instance] 0 #455
[attach-enode] #455 0
[end-of-instance]
[mk-app] #455 = #447 #407
[mk-quant] #456 prelude_i_inv 2 #451 #455
[attach-var-names] #456 (|i| ; |Int|) (|bits| ; |Int|)
[mk-app] #453 charInv #123
[attach-meaning] #393 arith 55295
[attach-meaning] #413 arith 57344
[attach-meaning] #415 arith 1114111
[mk-app] #454 = #453 #424
[mk-app] #457 pattern #453
[mk-quant] #458 prelude_char_inv 1 #457 #454
[attach-var-names] #458 (|i| ; |Int|)
[attach-meaning] #366 arith (- 1)
[mk-app] #459 * #366 #123
[inst-discovered] theory-solving 0 arith# ; #340
[mk-app] #459 = #340 #349
[instance] 0 #459
[attach-enode] #459 0
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #459 * #366 #123
[mk-app] #460 Int
[attach-meaning] #460 arith (- 57344)
[attach-meaning] #413 arith 57344
[inst-discovered] theory-solving 0 arith# ; #421
[mk-app] #459 = #421 #438
[instance] 0 #459
[attach-enode] #459 0
[end-of-instance]
[mk-app] #459 = #453 #437
[mk-quant] #460 prelude_char_inv 1 #457 #459
[attach-var-names] #460 (|i| ; |Int|)
[mk-app] #461 has_type #166 #185
[mk-app] #462 pattern #461
[mk-quant] #463 prelude_has_type_int 1 #462 #461
[attach-var-names] #463 (|x| ; |Int|)
[mk-app] #464 has_type #166 #196
[mk-app] #465 => #340 #464
[mk-app] #466 pattern #464
[mk-quant] #467 prelude_has_type_nat 1 #466 #465
[attach-var-names] #467 (|x| ; |Int|)
[attach-meaning] #366 arith (- 1)
[mk-app] #468 * #366 #123
[inst-discovered] theory-solving 0 arith# ; #340
[mk-app] #468 = #340 #349
[instance] 0 #468
[attach-enode] #468 0
[end-of-instance]
[mk-app] #468 or #346 #464
[mk-app] #469 => #349 #464
[inst-discovered] theory-solving 0 basic# ; #469
[mk-app] #470 = #469 #468
[instance] 0 #470
[attach-enode] #470 0
[end-of-instance]
[mk-quant] #469 prelude_has_type_nat 1 #466 #468
[attach-var-names] #469 (|x| ; |Int|)
[mk-app] #470 uInv #270 #123
[mk-app] #471 has_type #166 #204
[mk-app] #472 => #470 #471
[mk-app] #473 pattern #471
[mk-quant] #474 prelude_has_type_usize 1 #473 #472
[attach-var-names] #474 (|x| ; |Int|)
[mk-app] #475 not #470
[mk-app] #476 or #475 #471
[inst-discovered] theory-solving 0 basic# ; #472
[mk-app] #477 = #472 #476
[instance] 0 #477
[attach-enode] #477 0
[end-of-instance]
[mk-quant] #477 prelude_has_type_usize 1 #473 #476
[attach-var-names] #477 (|x| ; |Int|)
[mk-app] #478 iInv #270 #123
[mk-app] #479 has_type #166 #212
[mk-app] #480 => #478 #479
[mk-app] #481 pattern #479
[mk-quant] #482 prelude_has_type_isize 1 #481 #480
[attach-var-names] #482 (|x| ; |Int|)
[mk-app] #483 not #478
[mk-app] #484 or #483 #479
[inst-discovered] theory-solving 0 basic# ; #480
[mk-app] #485 = #480 #484
[instance] 0 #485
[attach-enode] #485 0
[end-of-instance]
[mk-quant] #485 prelude_has_type_isize 1 #481 #484
[attach-var-names] #485 (|x| ; |Int|)
[mk-app] #486 has_type #166 #221
[mk-app] #487 => #443 #486
[mk-app] #488 pattern #486
[mk-quant] #489 prelude_has_type_uint 2 #488 #487
[attach-var-names] #489 (|x| ; |Int|) (|bits| ; |Int|)
[mk-app] #490 not #443
[mk-app] #491 or #490 #486
[inst-discovered] theory-solving 0 basic# ; #487
[mk-app] #492 = #487 #491
[instance] 0 #492
[attach-enode] #492 0
[end-of-instance]
[mk-quant] #492 prelude_has_type_uint 2 #488 #491
[attach-var-names] #492 (|x| ; |Int|) (|bits| ; |Int|)
[mk-app] #493 has_type #166 #229
[mk-app] #494 => #447 #493
[mk-app] #495 pattern #493
[mk-quant] #496 prelude_has_type_sint 2 #495 #494
[attach-var-names] #496 (|x| ; |Int|) (|bits| ; |Int|)
[mk-app] #497 not #447
[mk-app] #498 or #497 #493
[inst-discovered] theory-solving 0 basic# ; #494
[mk-app] #499 = #494 #498
[instance] 0 #499
[attach-enode] #499 0
[end-of-instance]
[mk-quant] #499 prelude_has_type_sint 2 #495 #498
[attach-var-names] #499 (|x| ; |Int|) (|bits| ; |Int|)
[mk-app] #500 has_type #166 #237
[mk-app] #501 => #443 #500
[mk-app] #502 pattern #500
[mk-quant] #503 prelude_has_type_sint 2 #502 #501
[attach-var-names] #503 (|x| ; |Int|) (|bits| ; |Int|)
[mk-app] #504 or #490 #500
[inst-discovered] theory-solving 0 basic# ; #501
[mk-app] #505 = #501 #504
[instance] 0 #505
[attach-enode] #505 0
[end-of-instance]
[mk-quant] #505 prelude_has_type_sint 2 #502 #504
[attach-var-names] #505 (|x| ; |Int|) (|bits| ; |Int|)
[mk-app] #506 has_type #166 #245
[mk-app] #507 => #453 #506
[mk-app] #508 pattern #506
[mk-quant] #509 prelude_has_type_char 1 #508 #507
[attach-var-names] #509 (|x| ; |Int|)
[mk-app] #510 not #453
[mk-app] #511 or #510 #506
[inst-discovered] theory-solving 0 basic# ; #507
[mk-app] #512 = #507 #511
[instance] 0 #512
[attach-enode] #512 0
[end-of-instance]
[mk-quant] #512 prelude_has_type_char 1 #508 #511
[attach-var-names] #512 (|x| ; |Int|)
[mk-app] #513 <= #337 #187
[mk-app] #514 => #197 #513
[mk-quant] #515 prelude_unbox_int 1 #199 #514
[attach-var-names] #515 (|x| ; |Poly|)
[attach-meaning] #366 arith (- 1)
[mk-app] #516 * #366 #187
[mk-app] #517 >= #187 #337
[inst-discovered] theory-solving 0 arith# ; #513
[mk-app] #516 = #513 #517
[instance] 0 #516
[attach-enode] #516 0
[end-of-instance]
[mk-app] #516 or #201 #517
[mk-app] #518 => #197 #517
[inst-discovered] theory-solving 0 basic# ; #518
[mk-app] #519 = #518 #516
[instance] 0 #519
[attach-enode] #519 0
[end-of-instance]
[mk-quant] #518 prelude_unbox_int 1 #199 #516
[attach-var-names] #518 (|x| ; |Poly|)
[mk-app] #519 uInv #270 #187
[mk-app] #520 => #205 #519
[mk-quant] #521 prelude_unbox_usize 1 #207 #520
[attach-var-names] #521 (|x| ; |Poly|)
[mk-app] #522 or #209 #519
[inst-discovered] theory-solving 0 basic# ; #520
[mk-app] #523 = #520 #522
[instance] 0 #523
[attach-enode] #523 0
[end-of-instance]
[mk-quant] #523 prelude_unbox_usize 1 #207 #522
[attach-var-names] #523 (|x| ; |Poly|)
[mk-app] #524 iInv #270 #187
[mk-app] #525 => #213 #524
[mk-quant] #526 prelude_unbox_isize 1 #215 #525
[attach-var-names] #526 (|x| ; |Poly|)
[mk-app] #527 or #217 #524
[inst-discovered] theory-solving 0 basic# ; #525
[mk-app] #528 = #525 #527
[instance] 0 #528
[attach-enode] #528 0
[end-of-instance]
[mk-quant] #528 prelude_unbox_isize 1 #215 #527
[attach-var-names] #528 (|x| ; |Poly|)
[mk-app] #529 uInv #220 #187
[mk-app] #530 => #222 #529
[mk-quant] #531 prelude_unbox_uint 2 #224 #530
[attach-var-names] #531 (|x| ; |Poly|) (|bits| ; |Int|)
[mk-app] #532 or #226 #529
[inst-discovered] theory-solving 0 basic# ; #530
[mk-app] #533 = #530 #532
[instance] 0 #533
[attach-enode] #533 0
[end-of-instance]
[mk-quant] #533 prelude_unbox_uint 2 #224 #532
[attach-var-names] #533 (|x| ; |Poly|) (|bits| ; |Int|)
[mk-app] #534 iInv #220 #187
[mk-app] #535 => #230 #534
[mk-quant] #536 prelude_unbox_sint 2 #232 #535
[attach-var-names] #536 (|x| ; |Poly|) (|bits| ; |Int|)
[mk-app] #537 or #234 #534
[inst-discovered] theory-solving 0 basic# ; #535
[mk-app] #538 = #535 #537
[instance] 0 #538
[attach-enode] #538 0
[end-of-instance]
[mk-quant] #538 prelude_unbox_sint 2 #232 #537
[attach-var-names] #538 (|x| ; |Poly|) (|bits| ; |Int|)
[mk-app] #539 => #238 #529
[mk-quant] #540 prelude_unbox_sint 2 #240 #539
[attach-var-names] #540 (|x| ; |Poly|) (|bits| ; |Int|)
[mk-app] #541 or #242 #529
[inst-discovered] theory-solving 0 basic# ; #539
[mk-app] #542 = #539 #541
[instance] 0 #542
[attach-enode] #542 0
[end-of-instance]
[mk-quant] #542 prelude_unbox_sint 2 #240 #541
[attach-var-names] #542 (|x| ; |Poly|) (|bits| ; |Int|)
[mk-app] #543 Add #220 #123
[mk-app] #544 + #220 #123
[mk-app] #545 = #543 #544
[mk-app] #546 pattern #543
[mk-quant] #547 prelude_add 2 #546 #545
[attach-var-names] #547 (|y| ; |Int|) (|x| ; |Int|)
[mk-app] #548 + #123 #220
[inst-discovered] theory-solving 0 arith# ; #544
[mk-app] #549 = #544 #548
[instance] 0 #549
[attach-enode] #549 0
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #549 * #366 #123
[attach-meaning] #366 arith (- 1)
[mk-app] #550 * #366 #220
[mk-app] #551 + #549 #550 #543
[attach-meaning] #366 arith (- 1)
[mk-app] #552 * #366 #543
[mk-app] #553 + #123 #220 #552
[mk-app] #549 = #553 #337
[mk-app] #550 = #543 #548
[inst-discovered] theory-solving 0 arith# ; #550
[mk-app] #551 = #550 #549
[instance] 0 #551
[attach-enode] #551 0
[end-of-instance]
[mk-quant] #548 prelude_add 2 #546 #549
[attach-var-names] #548 (|y| ; |Int|) (|x| ; |Int|)
[mk-app] #550 Sub #220 #123
[mk-app] #551 - #220 #123
[mk-app] #554 = #550 #551
[mk-app] #555 pattern #550
[mk-quant] #556 prelude_sub 2 #555 #554
[attach-var-names] #556 (|y| ; |Int|) (|x| ; |Int|)
[attach-meaning] #366 arith (- 1)
[mk-app] #557 * #366 #123
[mk-app] #558 + #220 #557
[inst-discovered] theory-solving 0 arith# ; #551
[mk-app] #559 = #551 #558
[instance] 0 #559
[attach-enode] #559 0
[end-of-instance]
[mk-app] #559 + #557 #220
[inst-discovered] theory-solving 0 arith# ; #558
[mk-app] #560 = #558 #559
[instance] 0 #560
[attach-enode] #560 0
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #560 * #366 #220
[mk-app] #561 + #123 #560 #550
[mk-app] #562 = #561 #337
[mk-app] #563 = #550 #559
[inst-discovered] theory-solving 0 arith# ; #563
[mk-app] #564 = #563 #562
[instance] 0 #564
[attach-enode] #564 0
[end-of-instance]
[mk-quant] #563 prelude_sub 2 #555 #562
[attach-var-names] #563 (|y| ; |Int|) (|x| ; |Int|)
[mk-app] #557 Mul #220 #123
[mk-app] #559 * #220 #123
[mk-app] #558 = #557 #559
[mk-app] #564 pattern #557
[mk-quant] #565 prelude_mul 2 #564 #558
[attach-var-names] #565 (|y| ; |Int|) (|x| ; |Int|)
[mk-app] #566 * #123 #220
[inst-discovered] theory-solving 0 arith# ; #559
[mk-app] #567 = #559 #566
[instance] 0 #567
[attach-enode] #567 0
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #567 * #366 #566
[mk-app] #568 + #557 #567
[mk-app] #569 = #568 #337
[mk-app] #570 = #557 #566
[inst-discovered] theory-solving 0 arith# ; #570
[mk-app] #571 = #570 #569
[instance] 0 #571
[attach-enode] #571 0
[end-of-instance]
[mk-quant] #570 prelude_mul 2 #564 #569
[attach-var-names] #570 (|y| ; |Int|) (|x| ; |Int|)
[mk-app] #571 EucDiv #220 #123
[mk-app] #572 div #220 #123
[mk-app] #573 = #571 #572
[mk-app] #574 pattern #571
[mk-quant] #575 prelude_eucdiv 2 #574 #573
[attach-var-names] #575 (|y| ; |Int|) (|x| ; |Int|)
[attach-meaning] #366 arith (- 1)
[mk-app] #576 * #366 #572
[mk-app] #577 + #571 #576
[mk-app] #578 = #577 #337
[inst-discovered] theory-solving 0 arith# ; #573
[mk-app] #579 = #573 #578
[instance] 0 #579
[attach-enode] #579 0
[end-of-instance]
[mk-quant] #579 prelude_eucdiv 2 #574 #578
[attach-var-names] #579 (|y| ; |Int|) (|x| ; |Int|)
[mk-app] #580 EucMod #220 #123
[mk-app] #581 mod #220 #123
[mk-app] #582 = #580 #581
[mk-app] #583 pattern #580
[mk-quant] #584 prelude_eucmod 2 #583 #582
[attach-var-names] #584 (|y| ; |Int|) (|x| ; |Int|)
[attach-meaning] #366 arith (- 1)
[mk-app] #585 * #366 #581
[mk-app] #586 + #580 #585
[mk-app] #587 = #586 #337
[inst-discovered] theory-solving 0 arith# ; #582
[mk-app] #588 = #582 #587
[instance] 0 #588
[attach-enode] #588 0
[end-of-instance]
[mk-quant] #588 prelude_eucmod 2 #583 #587
[attach-var-names] #588 (|y| ; |Int|) (|x| ; |Int|)
[mk-app] #589 RAdd #8 #7
[mk-app] #590 + #8 #7
[mk-app] #591 = #589 #590
[mk-app] #592 pattern #589
[mk-quant] #593 prelude_radd 2 #592 #591
[attach-var-names] #593 (|y| ; |Real|) (|x| ; |Real|)
[mk-app] #594 + #7 #8
[inst-discovered] theory-solving 0 arith# ; #590
[mk-app] #595 = #590 #594
[instance] 0 #595
[attach-enode] #595 0
[end-of-instance]
[mk-app] #595 Real
[attach-meaning] #595 arith (- 1)
[mk-app] #596 * #595 #7
[attach-meaning] #595 arith (- 1)
[mk-app] #597 * #595 #8
[mk-app] #598 Real
[attach-meaning] #598 arith 0
[mk-app] #599 + #596 #597 #589
[attach-meaning] #595 arith (- 1)
[mk-app] #600 * #595 #589
[mk-app] #601 + #7 #8 #600
[mk-app] #596 = #601 #598
[mk-app] #597 = #589 #594
[inst-discovered] theory-solving 0 arith# ; #597
[mk-app] #599 = #597 #596
[instance] 0 #599
[attach-enode] #599 0
[end-of-instance]
[mk-quant] #594 prelude_radd 2 #592 #596
[attach-var-names] #594 (|y| ; |Real|) (|x| ; |Real|)
[mk-app] #597 RSub #8 #7
[mk-app] #599 - #8 #7
[mk-app] #602 = #597 #599
[mk-app] #603 pattern #597
[mk-quant] #604 prelude_rsub 2 #603 #602
[attach-var-names] #604 (|y| ; |Real|) (|x| ; |Real|)
[attach-meaning] #595 arith (- 1)
[mk-app] #605 * #595 #7
[mk-app] #606 + #8 #605
[inst-discovered] theory-solving 0 arith# ; #599
[mk-app] #607 = #599 #606
[instance] 0 #607
[attach-enode] #607 0
[end-of-instance]
[mk-app] #607 + #605 #8
[inst-discovered] theory-solving 0 arith# ; #606
[mk-app] #608 = #606 #607
[instance] 0 #608
[attach-enode] #608 0
[end-of-instance]
[attach-meaning] #595 arith (- 1)
[mk-app] #608 * #595 #8
[mk-app] #609 + #7 #608 #597
[mk-app] #610 = #609 #598
[mk-app] #611 = #597 #607
[inst-discovered] theory-solving 0 arith# ; #611
[mk-app] #612 = #611 #610
[instance] 0 #612
[attach-enode] #612 0
[end-of-instance]
[mk-quant] #611 prelude_rsub 2 #603 #610
[attach-var-names] #611 (|y| ; |Real|) (|x| ; |Real|)
[mk-app] #605 RMul #8 #7
[mk-app] #607 * #8 #7
[mk-app] #606 = #605 #607
[mk-app] #612 pattern #605
[mk-quant] #613 prelude_rmul 2 #612 #606
[attach-var-names] #613 (|y| ; |Real|) (|x| ; |Real|)
[mk-app] #614 * #7 #8
[inst-discovered] theory-solving 0 arith# ; #607
[mk-app] #615 = #607 #614
[instance] 0 #615
[attach-enode] #615 0
[end-of-instance]
[attach-meaning] #595 arith (- 1)
[mk-app] #615 * #595 #614
[mk-app] #616 + #605 #615
[mk-app] #617 = #616 #598
[mk-app] #618 = #605 #614
[inst-discovered] theory-solving 0 arith# ; #618
[mk-app] #619 = #618 #617
[instance] 0 #619
[attach-enode] #619 0
[end-of-instance]
[mk-quant] #618 prelude_rmul 2 #612 #617
[attach-var-names] #618 (|y| ; |Real|) (|x| ; |Real|)
[mk-app] #619 RDiv #8 #7
[mk-app] #620 / #8 #7
[mk-app] #621 = #619 #620
[mk-app] #622 pattern #619
[mk-quant] #623 prelude_rdiv 2 #622 #621
[attach-var-names] #623 (|y| ; |Real|) (|x| ; |Real|)
[attach-meaning] #595 arith (- 1)
[mk-app] #624 * #595 #620
[mk-app] #625 + #619 #624
[mk-app] #626 = #625 #598
[inst-discovered] theory-solving 0 arith# ; #621
[mk-app] #627 = #621 #626
[instance] 0 #627
[attach-enode] #627 0
[end-of-instance]
[mk-quant] #627 prelude_rdiv 2 #622 #626
[attach-var-names] #627 (|y| ; |Real|) (|x| ; |Real|)
[mk-app] #628 <= #337 #220
[mk-app] #629 and #628 #340
[mk-app] #630 <= #337 #557
[mk-app] #631 => #629 #630
[mk-quant] #632 prelude_mul_nats 2 #564 #631
[attach-var-names] #632 (|y| ; |Int|) (|x| ; |Int|)
[attach-meaning] #366 arith (- 1)
[mk-app] #633 >= #220 #337
[inst-discovered] theory-solving 0 arith# ; #628
[mk-app] #634 = #628 #633
[instance] 0 #634
[attach-enode] #634 0
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #634 * #366 #123
[inst-discovered] theory-solving 0 arith# ; #340
[mk-app] #634 = #340 #349
[instance] 0 #634
[attach-enode] #634 0
[end-of-instance]
[mk-app] #634 and #633 #349
[attach-meaning] #366 arith (- 1)
[mk-app] #635 * #366 #557
[mk-app] #636 >= #557 #337
[inst-discovered] theory-solving 0 arith# ; #630
[mk-app] #635 = #630 #636
[instance] 0 #635
[attach-enode] #635 0
[end-of-instance]
[mk-app] #635 not #634
[mk-app] #637 or #635 #636
[mk-app] #638 => #634 #636
[inst-discovered] theory-solving 0 basic# ; #638
[mk-app] #639 = #638 #637
[instance] 0 #639
[attach-enode] #639 0
[end-of-instance]
[mk-quant] #638 prelude_mul_nats 2 #564 #637
[attach-var-names] #638 (|y| ; |Int|) (|x| ; |Int|)
[mk-app] #639 < #337 #123
[mk-app] #640 and #628 #639
[mk-app] #641 <= #337 #571
[mk-app] #642 <= #571 #220
[mk-app] #643 and #641 #642
[mk-app] #644 => #640 #643
[mk-quant] #645 prelude_div_unsigned_in_bounds 2 #574 #644
[attach-var-names] #645 (|y| ; |Int|) (|x| ; |Int|)
[attach-meaning] #366 arith (- 1)
[inst-discovered] theory-solving 0 arith# ; #628
[mk-app] #646 = #628 #633
[instance] 0 #646
[attach-enode] #646 0
[end-of-instance]
[mk-app] #646 <= #123 #337
[mk-app] #647 not #646
[inst-discovered] theory-solving 0 arith# ; #639
[mk-app] #648 = #639 #647
[instance] 0 #648
[attach-enode] #648 0
[end-of-instance]
[mk-app] #648 and #633 #647
[attach-meaning] #366 arith (- 1)
[mk-app] #649 * #366 #571
[mk-app] #650 >= #571 #337
[inst-discovered] theory-solving 0 arith# ; #641
[mk-app] #649 = #641 #650
[instance] 0 #649
[attach-enode] #649 0
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #649 + #560 #571
[attach-meaning] #366 arith (- 1)
[mk-app] #651 * #366 #571
[mk-app] #652 + #220 #651
[mk-app] #649 >= #652 #337
[inst-discovered] theory-solving 0 arith# ; #642
[mk-app] #653 = #642 #649
[instance] 0 #653
[attach-enode] #653 0
[end-of-instance]
[mk-app] #653 and #650 #649
[mk-app] #654 not #648
[mk-app] #655 or #654 #653
[mk-app] #656 => #648 #653
[inst-discovered] theory-solving 0 basic# ; #656
[mk-app] #657 = #656 #655
[instance] 0 #657
[attach-enode] #657 0
[end-of-instance]
[mk-quant] #656 prelude_div_unsigned_in_bounds 2 #574 #655
[attach-var-names] #656 (|y| ; |Int|) (|x| ; |Int|)
[mk-app] #657 <= #337 #580
[mk-app] #658 < #580 #123
[mk-app] #659 and #657 #658
[mk-app] #660 => #640 #659
[mk-quant] #661 prelude_mod_unsigned_in_bounds 2 #583 #660
[attach-var-names] #661 (|y| ; |Int|) (|x| ; |Int|)
[attach-meaning] #366 arith (- 1)
[inst-discovered] theory-solving 0 arith# ; #628
[mk-app] #662 = #628 #633
[instance] 0 #662
[attach-enode] #662 0
[end-of-instance]
[inst-discovered] theory-solving 0 arith# ; #639
[mk-app] #662 = #639 #647
[instance] 0 #662
[attach-enode] #662 0
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #662 * #366 #580
[mk-app] #663 >= #580 #337
[inst-discovered] theory-solving 0 arith# ; #657
[mk-app] #662 = #657 #663
[instance] 0 #662
[attach-enode] #662 0
[end-of-instance]
[mk-app] #662 <= #123 #580
[mk-app] #664 not #662
[inst-discovered] theory-solving 0 arith# ; #658
[mk-app] #665 = #658 #664
[instance] 0 #665
[attach-enode] #665 0
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #665 * #366 #580
[mk-app] #666 + #123 #665
[mk-app] #667 <= #666 #337
[inst-discovered] theory-solving 0 arith# ; #662
[mk-app] #668 = #662 #667
[instance] 0 #668
[attach-enode] #668 0
[end-of-instance]
[mk-app] #668 not #667
[mk-app] #669 and #663 #668
[mk-app] #670 or #654 #669
[mk-app] #671 => #648 #669
[inst-discovered] theory-solving 0 basic# ; #671
[mk-app] #672 = #671 #670
[instance] 0 #672
[attach-enode] #672 0
[end-of-instance]
[mk-quant] #671 prelude_mod_unsigned_in_bounds 2 #583 #670
[attach-var-names] #671 (|y| ; |Int|) (|x| ; |Int|)
[mk-app] #662 %I #44
[mk-app] #664 uInv #123 #662
[mk-app] #672 %I #33
[mk-app] #673 uInv #123 #672
[mk-app] #674 and #664 #673
[mk-app] #675 bitxor #44 #33
[mk-app] #676 uInv #123 #675
[mk-app] #677 => #674 #676
[mk-app] #678 uClip #123 #675
[mk-app] #679 pattern #678
[mk-quant] #680 prelude_bit_xor_u_inv 3 #679 #677
[attach-var-names] #680 (|bits| ; |Int|) (|y| ; |Poly|) (|x| ; |Poly|)
[mk-app] #681 not #674
[mk-app] #682 or #681 #676
[inst-discovered] theory-solving 0 basic# ; #677
[mk-app] #683 = #677 #682
[instance] 0 #683
[attach-enode] #683 0
[end-of-instance]
[mk-quant] #683 prelude_bit_xor_u_inv 3 #679 #682
[attach-var-names] #683 (|bits| ; |Int|) (|y| ; |Poly|) (|x| ; |Poly|)
[mk-app] #684 iInv #123 #662
[mk-app] #685 iInv #123 #672
[mk-app] #686 and #684 #685
[mk-app] #687 iInv #123 #675
[mk-app] #688 => #686 #687
[mk-app] #689 iClip #123 #675
[mk-app] #690 pattern #689
[mk-quant] #691 prelude_bit_xor_i_inv 3 #690 #688
[attach-var-names] #691 (|bits| ; |Int|) (|y| ; |Poly|) (|x| ; |Poly|)
[mk-app] #692 not #686
[mk-app] #693 or #692 #687
[inst-discovered] theory-solving 0 basic# ; #688
[mk-app] #694 = #688 #693
[instance] 0 #694
[attach-enode] #694 0
[end-of-instance]
[mk-quant] #694 prelude_bit_xor_i_inv 3 #690 #693
[attach-var-names] #694 (|bits| ; |Int|) (|y| ; |Poly|) (|x| ; |Poly|)
[mk-app] #695 bitor #44 #33
[mk-app] #696 uInv #123 #695
[mk-app] #697 => #674 #696
[mk-app] #698 uClip #123 #695
[mk-app] #699 pattern #698
[mk-quant] #700 prelude_bit_or_u_inv 3 #699 #697
[attach-var-names] #700 (|bits| ; |Int|) (|y| ; |Poly|) (|x| ; |Poly|)
[mk-app] #701 or #681 #696
[inst-discovered] theory-solving 0 basic# ; #697
[mk-app] #702 = #697 #701
[instance] 0 #702
[attach-enode] #702 0
[end-of-instance]
[mk-quant] #702 prelude_bit_or_u_inv 3 #699 #701
[attach-var-names] #702 (|bits| ; |Int|) (|y| ; |Poly|) (|x| ; |Poly|)
[mk-app] #703 iInv #123 #695
[mk-app] #704 => #686 #703
[mk-app] #705 iClip #123 #695
[mk-app] #706 pattern #705
[mk-quant] #707 prelude_bit_or_i_inv 3 #706 #704
[attach-var-names] #707 (|bits| ; |Int|) (|y| ; |Poly|) (|x| ; |Poly|)
[mk-app] #708 or #692 #703
[inst-discovered] theory-solving 0 basic# ; #704
[mk-app] #709 = #704 #708
[instance] 0 #709
[attach-enode] #709 0
[end-of-instance]
[mk-quant] #709 prelude_bit_or_i_inv 3 #706 #708
[attach-var-names] #709 (|bits| ; |Int|) (|y| ; |Poly|) (|x| ; |Poly|)
[mk-app] #710 bitand #44 #33
[mk-app] #711 uInv #123 #710
[mk-app] #712 => #674 #711
[mk-app] #713 uClip #123 #710
[mk-app] #714 pattern #713
[mk-quant] #715 prelude_bit_and_u_inv 3 #714 #712
[attach-var-names] #715 (|bits| ; |Int|) (|y| ; |Poly|) (|x| ; |Poly|)
[mk-app] #716 or #681 #711
[inst-discovered] theory-solving 0 basic# ; #712
[mk-app] #717 = #712 #716
[instance] 0 #717
[attach-enode] #717 0
[end-of-instance]
[mk-quant] #717 prelude_bit_and_u_inv 3 #714 #716
[attach-var-names] #717 (|bits| ; |Int|) (|y| ; |Poly|) (|x| ; |Poly|)
[mk-app] #718 iInv #123 #710
[mk-app] #719 => #686 #718
[mk-app] #720 iClip #123 #710
[mk-app] #721 pattern #720
[mk-quant] #722 prelude_bit_and_i_inv 3 #721 #719
[attach-var-names] #722 (|bits| ; |Int|) (|y| ; |Poly|) (|x| ; |Poly|)
[mk-app] #723 or #692 #718
[inst-discovered] theory-solving 0 basic# ; #719
[mk-app] #724 = #719 #723
[instance] 0 #724
[attach-enode] #724 0
[end-of-instance]
[mk-quant] #724 prelude_bit_and_i_inv 3 #721 #723
[attach-var-names] #724 (|bits| ; |Int|) (|y| ; |Poly|) (|x| ; |Poly|)
[mk-app] #725 <= #337 #672
[mk-app] #726 and #664 #725
[mk-app] #727 bitshr #44 #33
[mk-app] #728 uInv #123 #727
[mk-app] #729 => #726 #728
[mk-app] #730 uClip #123 #727
[mk-app] #731 pattern #730
[mk-quant] #732 prelude_bit_shr_u_inv 3 #731 #729
[attach-var-names] #732 (|bits| ; |Int|) (|y| ; |Poly|) (|x| ; |Poly|)
[attach-meaning] #366 arith (- 1)
[mk-app] #733 * #366 #672
[mk-app] #734 >= #672 #337
[inst-discovered] theory-solving 0 arith# ; #725
[mk-app] #733 = #725 #734
[instance] 0 #733
[attach-enode] #733 0
[end-of-instance]
[mk-app] #733 and #664 #734
[mk-app] #735 not #733
[mk-app] #736 or #735 #728
[mk-app] #737 => #733 #728
[inst-discovered] theory-solving 0 basic# ; #737
[mk-app] #738 = #737 #736
[instance] 0 #738
[attach-enode] #738 0
[end-of-instance]
[mk-quant] #737 prelude_bit_shr_u_inv 3 #731 #736
[attach-var-names] #737 (|bits| ; |Int|) (|y| ; |Poly|) (|x| ; |Poly|)
[mk-app] #738 and #684 #725
[mk-app] #739 iInv #123 #727
[mk-app] #740 => #738 #739
[mk-app] #741 iClip #123 #727
[mk-app] #742 pattern #741
[mk-quant] #743 prelude_bit_shr_i_inv 3 #742 #740
[attach-var-names] #743 (|bits| ; |Int|) (|y| ; |Poly|) (|x| ; |Poly|)
[attach-meaning] #366 arith (- 1)
[mk-app] #744 * #366 #672
[inst-discovered] theory-solving 0 arith# ; #725
[mk-app] #744 = #725 #734
[instance] 0 #744
[attach-enode] #744 0
[end-of-instance]
[mk-app] #744 and #684 #734
[mk-app] #745 not #744
[mk-app] #746 or #745 #739
[mk-app] #747 => #744 #739
[inst-discovered] theory-solving 0 basic# ; #747
[mk-app] #748 = #747 #746
[instance] 0 #748
[attach-enode] #748 0
[end-of-instance]
[mk-quant] #747 prelude_bit_shr_i_inv 3 #742 #746
[attach-var-names] #747 (|bits| ; |Int|) (|y| ; |Poly|) (|x| ; |Poly|)
[mk-app] #748 = #123 #337
[mk-app] #749 not #748
[mk-app] #750 singular_mod #220 #123
[mk-app] #751 = #580 #750
[mk-app] #752 => #749 #751
[mk-app] #753 pattern #750
[mk-quant] #754 prelude_singularmod 2 #753 #752
[attach-var-names] #754 (|y| ; |Int|) (|x| ; |Int|)
[mk-app] #755 or #748 #751
[inst-discovered] theory-solving 0 basic# ; #752
[mk-app] #756 = #752 #755
[instance] 0 #756
[attach-enode] #756 0
[end-of-instance]
[mk-quant] #756 prelude_singularmod 2 #753 #755
[attach-var-names] #756 (|y| ; |Int|) (|x| ; |Int|)
[mk-app] #757 check_decrease_height #44 #33 #129
[mk-app] #758 height #44
[mk-app] #759 height #33
[mk-app] #760 height_lt #758 #759
[mk-app] #761 = #758 #759
[mk-app] #762 and #761 #129
[mk-app] #763 or #760 #762
[mk-app] #764 = #757 #763
[mk-app] #765 pattern #757
[mk-quant] #766 prelude_check_decrease_height 3 #765 #764
[attach-var-names] #766 (|otherwise| ; |Bool|) (|prev| ; |Poly|) (|cur| ; |Poly|)
[mk-app] #767 I #220
[mk-app] #768 height #767
[mk-app] #769 height #166
[mk-app] #770 height_lt #768 #769
[mk-app] #771 < #220 #123
[mk-app] #772 and #628 #771
[mk-app] #773 = #770 #772
[mk-app] #774 pattern #770
[mk-quant] #775 prelude_check_decrease_int_height 2 #774 #773
[attach-var-names] #775 (|prev| ; |Int|) (|cur| ; |Int|)
[attach-meaning] #366 arith (- 1)
[inst-discovered] theory-solving 0 arith# ; #628
[mk-app] #776 = #628 #633
[instance] 0 #776
[attach-enode] #776 0
[end-of-instance]
[mk-app] #776 <= #123 #220
[mk-app] #777 not #776
[inst-discovered] theory-solving 0 arith# ; #771
[mk-app] #778 = #771 #777
[instance] 0 #778
[attach-enode] #778 0
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #778 + #123 #560
[mk-app] #779 <= #778 #337
[inst-discovered] theory-solving 0 arith# ; #776
[mk-app] #780 = #776 #779
[instance] 0 #780
[attach-enode] #780 0
[end-of-instance]
[mk-app] #780 not #779
[mk-app] #781 and #633 #780
[mk-app] #782 = #770 #781
[mk-quant] #783 prelude_check_decrease_int_height 2 #774 #782
[attach-var-names] #783 (|prev| ; |Int|) (|cur| ; |Int|)
[mk-var] #776 1
[mk-var] #777 0
[mk-app] #784 height_lt #776 #777
[mk-app] #785 partial-order #776 #777
[mk-app] #786 = #776 #777
[mk-app] #787 not #786
[mk-app] #788 and #785 #787
[mk-app] #789 = #784 #788
[mk-app] #790 pattern #784
[mk-quant] #791 prelude_height_lt 2 #790 #789
[attach-var-names] #791 (|y| ; |Height|) (|x| ; |Height|)
[mk-app] #792 fuel%vstd!function.axiom_fn_mut_call_requires.
[mk-app] #793 fuel%vstd!function.axiom_fn_mut_call_ensures.
[mk-app] #794 fuel%the_q!model.pow2.
[mk-app] #795 fuel%the_q!model.abs_int.
[mk-app] #796 fuel%the_q!model.max_int.
[mk-app] #797 fuel%the_q!model.divides.
[mk-app] #798 fuel%the_q!model.gcd_nat.
[mk-app] #799 fuel%the_q!model.gcd_int.
[mk-app] #800 fuel%the_q!model.bitlen.
[mk-app] #801 fuel%the_q!model.max_mag.
[mk-app] #802 fuel%the_q!model.fits_budget.
[mk-app] #803 fuel%the_q!model.magnitude_fits.
[mk-app] #804 fuel%the_q!model.impl&%0.wf.
[mk-app] #805 fuel%the_q!model.impl&%0.n.
[mk-app] #806 fuel%the_q!model.impl&%0.d.
[mk-app] #807 fuel%the_q!model.q_eq.
[mk-app] #808 fuel%the_q!model.q_le.
[mk-app] #809 fuel%the_q!model.q_lt.
[mk-app] #810 fuel%the_q!model.q_is.
[mk-app] #811 fuel%the_q!model.q_le_frac.
[mk-app] #812 fuel%the_q!model.q_ge_frac.
[mk-app] #813 fuel%the_q!model.precision_b.
[mk-app] #814 fuel%the_q!model.within_error_bound.
[mk-app] #815 fuel%the_q!model.within_error_bound_k.
[mk-app] #816 fuel%the_q!model.within_abs_error.
[mk-app] #817 fuel%the_q!types.MAX_MAG.
[mk-app] #818 fuel%vstd!array.group_array_axioms.
[mk-app] #819 fuel%vstd!function.group_function_axioms.
[mk-app] #820 fuel%vstd!imap.group_imap_lemmas.
[mk-app] #821 fuel%vstd!iset.group_iset_lemmas.
[mk-app] #822 fuel%vstd!laws_cmp.group_laws_cmp.
[mk-app] #823 fuel%vstd!laws_eq.bool_laws.group_laws_eq.
[mk-app] #824 fuel%vstd!laws_eq.u8_laws.group_laws_eq.
[mk-app] #825 fuel%vstd!laws_eq.i8_laws.group_laws_eq.
[mk-app] #826 fuel%vstd!laws_eq.u16_laws.group_laws_eq.
[mk-app] #827 fuel%vstd!laws_eq.i16_laws.group_laws_eq.
[mk-app] #828 fuel%vstd!laws_eq.u32_laws.group_laws_eq.
[mk-app] #829 fuel%vstd!laws_eq.i32_laws.group_laws_eq.
[mk-app] #830 fuel%vstd!laws_eq.u64_laws.group_laws_eq.
[mk-app] #831 fuel%vstd!laws_eq.i64_laws.group_laws_eq.
[mk-app] #832 fuel%vstd!laws_eq.u128_laws.group_laws_eq.
[mk-app] #833 fuel%vstd!laws_eq.i128_laws.group_laws_eq.
[mk-app] #834 fuel%vstd!laws_eq.usize_laws.group_laws_eq.
[mk-app] #835 fuel%vstd!laws_eq.isize_laws.group_laws_eq.
[mk-app] #836 fuel%vstd!laws_eq.tuple_1_laws.group_laws_eq.
[mk-app] #837 fuel%vstd!laws_eq.tuple_2_laws.group_laws_eq.
[mk-app] #838 fuel%vstd!laws_eq.tuple_3_laws.group_laws_eq.
[mk-app] #839 fuel%vstd!laws_eq.tuple_4_laws.group_laws_eq.
[mk-app] #840 fuel%vstd!laws_eq.tuple_5_laws.group_laws_eq.
[mk-app] #841 fuel%vstd!laws_eq.tuple_6_laws.group_laws_eq.
[mk-app] #842 fuel%vstd!laws_eq.tuple_7_laws.group_laws_eq.
[mk-app] #843 fuel%vstd!laws_eq.tuple_8_laws.group_laws_eq.
[mk-app] #844 fuel%vstd!laws_eq.tuple_9_laws.group_laws_eq.
[mk-app] #845 fuel%vstd!laws_eq.tuple_10_laws.group_laws_eq.
[mk-app] #846 fuel%vstd!laws_eq.tuple_11_laws.group_laws_eq.
[mk-app] #847 fuel%vstd!laws_eq.tuple_12_laws.group_laws_eq.
[mk-app] #848 fuel%vstd!laws_eq.group_laws_eq.
[mk-app] #849 fuel%vstd!layout.group_align_properties.
[mk-app] #850 fuel%vstd!layout.group_layout_axioms.
[mk-app] #851 fuel%vstd!map.group_map_lemmas.
[mk-app] #852 fuel%vstd!multiset.group_multiset_axioms.
[mk-app] #853 fuel%vstd!raw_ptr.group_raw_ptr_axioms.
[mk-app] #854 fuel%vstd!seq.group_seq_lemmas.
[mk-app] #855 fuel%vstd!seq_lib.group_filter_ensures.
[mk-app] #856 fuel%vstd!seq_lib.group_seq_lib_default.
[mk-app] #857 fuel%vstd!set.group_set_lemmas.
[mk-app] #858 fuel%vstd!set_lib.group_set_lib_default.
[mk-app] #859 fuel%vstd!slice.group_slice_axioms.
[mk-app] #860 fuel%vstd!string.group_string_axioms.
[mk-app] #861 fuel%vstd!std_specs.bits.group_bits_axioms.
[mk-app] #862 fuel%vstd!std_specs.control_flow.group_control_flow_axioms.
[mk-app] #863 fuel%vstd!std_specs.iter.group_iter_axioms.
[mk-app] #864 fuel%vstd!std_specs.manually_drop.group_manually_drop_axioms.
[mk-app] #865 fuel%vstd!std_specs.btree.group_btree_axioms.
[mk-app] #866 fuel%vstd!std_specs.hash.group_hash_axioms.
[mk-app] #867 fuel%vstd!std_specs.range.group_range_axioms.
[mk-app] #868 fuel%vstd!std_specs.slice.group_slice_axioms.
[mk-app] #869 fuel%vstd!std_specs.vec.group_vec_axioms.
[mk-app] #870 fuel%vstd!std_specs.vecdeque.group_vec_dequeue_axioms.
[mk-app] #871 fuel%vstd!group_vstd_default.
[mk-app] #872 distinct #792 #793 #794 #795 #796 #797 #798 #799 #800 #801 #802 #803 #804 #805 #806 #807 #808 #809 #810 #811 #812 #813 #814 #815 #816 #817 #818 #819 #820 #821 #822 #823 #824 #825 #826 #827 #828 #829 #830 #831 #832 #833 #834 #835 #836 #837 #838 #839 #840 #841 #842 #843 #844 #845 #846 #847 #848 #849 #850 #851 #852 #853 #854 #855 #856 #857 #858 #859 #860 #861 #862 #863 #864 #865 #866 #867 #868 #869 #870 #871
[mk-app] #873 fuel_bool_default #819
[mk-app] #874 fuel_bool_default #792
[mk-app] #875 fuel_bool_default #793
[mk-app] #876 and #874 #875
[mk-app] #877 => #873 #876
[mk-app] #878 not #873
[mk-app] #879 or #878 #876
[inst-discovered] theory-solving 0 basic# ; #877
[mk-app] #880 = #877 #879
[instance] 0 #880
[attach-enode] #880 0
[end-of-instance]
[mk-app] #880 fuel_bool_default #848
[mk-app] #881 fuel_bool_default #823
[mk-app] #882 fuel_bool_default #824
[mk-app] #883 fuel_bool_default #825
[mk-app] #884 fuel_bool_default #826
[mk-app] #885 fuel_bool_default #827
[mk-app] #886 fuel_bool_default #828
[mk-app] #887 fuel_bool_default #829
[mk-app] #888 fuel_bool_default #830
[mk-app] #889 fuel_bool_default #831
[mk-app] #890 fuel_bool_default #832
[mk-app] #891 fuel_bool_default #833
[mk-app] #892 fuel_bool_default #834
[mk-app] #893 fuel_bool_default #835
[mk-app] #894 fuel_bool_default #836
[mk-app] #895 fuel_bool_default #837
[mk-app] #896 fuel_bool_default #838
[mk-app] #897 fuel_bool_default #839
[mk-app] #898 fuel_bool_default #840
[mk-app] #899 fuel_bool_default #841
[mk-app] #900 fuel_bool_default #842
[mk-app] #901 fuel_bool_default #843
[mk-app] #902 fuel_bool_default #844
[mk-app] #903 fuel_bool_default #845
[mk-app] #904 fuel_bool_default #846
[mk-app] #905 fuel_bool_default #847
[mk-app] #906 and #881 #882 #883 #884 #885 #886 #887 #888 #889 #890 #891 #892 #893 #894 #895 #896 #897 #898 #899 #900 #901 #902 #903 #904 #905
[mk-app] #907 => #880 #906
[mk-app] #908 not #880
[mk-app] #909 or #908 #906
[inst-discovered] theory-solving 0 basic# ; #907
[mk-app] #910 = #907 #909
[instance] 0 #910
[attach-enode] #910 0
[end-of-instance]
[mk-app] #910 fuel_bool_default #850
[mk-app] #911 fuel_bool_default #849
[mk-app] #912 => #910 #911
[mk-app] #913 not #910
[mk-app] #914 or #913 #911
[inst-discovered] theory-solving 0 basic# ; #912
[mk-app] #915 = #912 #914
[instance] 0 #915
[attach-enode] #915 0
[end-of-instance]
[mk-app] #915 fuel_bool_default #856
[mk-app] #916 fuel_bool_default #855
[mk-app] #917 => #915 #916
[mk-app] #918 not #915
[mk-app] #919 or #918 #916
[inst-discovered] theory-solving 0 basic# ; #917
[mk-app] #920 = #917 #919
[instance] 0 #920
[attach-enode] #920 0
[end-of-instance]
[mk-app] #920 fuel_bool_default #871
[mk-app] #921 fuel_bool_default #854
[mk-app] #922 fuel_bool_default #851
[mk-app] #923 fuel_bool_default #857
[mk-app] #924 fuel_bool_default #820
[mk-app] #925 fuel_bool_default #821
[mk-app] #926 fuel_bool_default #858
[mk-app] #927 fuel_bool_default #852
[mk-app] #928 fuel_bool_default #822
[mk-app] #929 fuel_bool_default #859
[mk-app] #930 fuel_bool_default #818
[mk-app] #931 fuel_bool_default #860
[mk-app] #932 fuel_bool_default #853
[mk-app] #933 fuel_bool_default #867
[mk-app] #934 fuel_bool_default #861
[mk-app] #935 fuel_bool_default #862
[mk-app] #936 fuel_bool_default #868
[mk-app] #937 fuel_bool_default #864
[mk-app] #938 fuel_bool_default #863
[mk-app] #939 fuel_bool_default #869
[mk-app] #940 fuel_bool_default #870
[mk-app] #941 fuel_bool_default #866
[mk-app] #942 fuel_bool_default #865
[mk-app] #943 and #921 #915 #922 #923 #924 #925 #926 #927 #873 #880 #928 #929 #930 #931 #932 #910 #933 #934 #935 #936 #937 #938 #939 #940 #941 #942
[mk-app] #944 => #920 #943
[mk-app] #945 not #920
[mk-app] #946 or #945 #943
[inst-discovered] theory-solving 0 basic# ; #944
[mk-app] #947 = #944 #946
[instance] 0 #947
[attach-enode] #947 0
[end-of-instance]
[mk-var] datatype#10 0
[mk-var] datatype#11 1
[mk-app] datatype#12 the_q!types.Q./Q datatype#10 datatype#11
[mk-app] datatype#13 pattern datatype#12
[mk-app] datatype#14 the_q!types.Q./Q/?num datatype#12
[mk-app] datatype#15 = datatype#10 datatype#14
[mk-quant] datatype#16 constructor_accessor_axiom 2 datatype#13 datatype#15
[attach-var-names] datatype#16 (;Int) (;Int)
[mk-app] datatype#17 the_q!types.Q./Q/?den datatype#12
[mk-app] datatype#18 = datatype#11 datatype#17
[mk-quant] datatype#19 constructor_accessor_axiom 2 datatype#13 datatype#18
[attach-var-names] datatype#19 (;Int) (;Int)
[mk-var] #947 0
[mk-app] #948 Poly%the_q!types.Q. #947
[mk-app] #949 %Poly%the_q!types.Q. #948
[mk-app] #950 = #947 #949
[mk-app] #951 pattern #948
[mk-quant] #952 internal_the_q__types__Q_box_axiom_definition 1 #951 #950
[attach-var-names] #952 (|x| ; |the_q!types.Q.|)
[mk-app] #953 TYPE%the_q!types.Q.
[mk-app] #954 has_type #34 #953
[mk-app] #955 %Poly%the_q!types.Q. #34
[mk-app] #956 Poly%the_q!types.Q. #955
[mk-app] #957 = #34 #956
[mk-app] #958 => #954 #957
[mk-app] #959 pattern #954
[mk-quant] #960 internal_the_q__types__Q_unbox_axiom_definition 1 #959 #958
[attach-var-names] #960 (|x| ; |Poly|)
[mk-app] #961 not #954
[mk-app] #962 or #961 #957
[inst-discovered] theory-solving 0 basic# ; #958
[mk-app] #963 = #958 #962
[instance] 0 #963
[attach-enode] #963 0
[end-of-instance]
[mk-quant] #963 internal_the_q__types__Q_unbox_axiom_definition 1 #959 #962
[attach-var-names] #963 (|x| ; |Poly|)
[attach-meaning] #273 arith 64
[mk-app] #964 iInv #273 #220
[attach-meaning] #273 arith 64
[mk-app] #965 iInv #273 #123
[mk-app] #966 and #964 #965
[mk-app] #967 the_q!types.Q./Q #220 #123
[mk-app] #968 Poly%the_q!types.Q. #967
[mk-app] #969 has_type #968 #953
[mk-app] #970 => #966 #969
[mk-app] #971 pattern #969
[mk-quant] #972 internal_the_q!types.Q./Q_constructor_definition 2 #971 #970
[attach-var-names] #972 (|_den!| ; |Int|) (|_num!| ; |Int|)
[mk-app] #973 not #966
[mk-app] #974 or #973 #969
[inst-discovered] theory-solving 0 basic# ; #970
[mk-app] #975 = #970 #974
[instance] 0 #975
[attach-enode] #975 0
[end-of-instance]
[mk-quant] #975 internal_the_q!types.Q./Q_constructor_definition 2 #971 #974
[attach-var-names] #975 (|_den!| ; |Int|) (|_num!| ; |Int|)
[mk-app] #976 the_q!types.Q./Q/num #947
[mk-app] #977 the_q!types.Q./Q/?num #947
[mk-app] #978 = #976 #977
[mk-app] #979 pattern #976
[mk-quant] #980 internal_the_q!types.Q./Q/num_accessor_definition 1 #979 #978
[attach-var-names] #980 (|x| ; |the_q!types.Q.|)
[attach-meaning] #273 arith 64
[mk-app] #981 the_q!types.Q./Q/num #955
[mk-app] #982 iInv #273 #981
[mk-app] #983 => #954 #982
[mk-app] #984 pattern #981 #954
[mk-quant] #985 internal_the_q!types.Q./Q/num_invariant_definition 1 #984 #983
[attach-var-names] #985 (|x| ; |Poly|)
[mk-app] #986 or #961 #982
[inst-discovered] theory-solving 0 basic# ; #983
[mk-app] #987 = #983 #986
[instance] 0 #987
[attach-enode] #987 0
[end-of-instance]
[mk-quant] #987 internal_the_q!types.Q./Q/num_invariant_definition 1 #984 #986
[attach-var-names] #987 (|x| ; |Poly|)
[mk-app] #988 the_q!types.Q./Q/den #947
[mk-app] #989 the_q!types.Q./Q/?den #947
[mk-app] #990 = #988 #989
[mk-app] #991 pattern #988
[mk-quant] #992 internal_the_q!types.Q./Q/den_accessor_definition 1 #991 #990
[attach-var-names] #992 (|x| ; |the_q!types.Q.|)
[attach-meaning] #273 arith 64
[mk-app] #993 the_q!types.Q./Q/den #955
[mk-app] #994 iInv #273 #993
[mk-app] #995 => #954 #994
[mk-app] #996 pattern #993 #954
[mk-quant] #997 internal_the_q!types.Q./Q/den_invariant_definition 1 #996 #995
[attach-var-names] #997 (|x| ; |Poly|)
[mk-app] #998 or #961 #994
[inst-discovered] theory-solving 0 basic# ; #995
[mk-app] #999 = #995 #998
[instance] 0 #999
[attach-enode] #999 0
[end-of-instance]
[mk-quant] #999 internal_the_q!types.Q./Q/den_invariant_definition 1 #996 #998
[attach-var-names] #999 (|x| ; |Poly|)
[mk-var] #1000 0
[mk-app] #1001 Poly%tuple%0. #1000
[mk-app] #1002 %Poly%tuple%0. #1001
[mk-app] #1003 = #1000 #1002
[mk-app] #1004 pattern #1001
[mk-quant] #1005 internal_crate__tuple__0_box_axiom_definition 1 #1004 #1003
[attach-var-names] #1005 (|x| ; |tuple%0.|)
[mk-app] #1006 TYPE%tuple%0.
[mk-app] #1007 has_type #34 #1006
[mk-app] #1008 %Poly%tuple%0. #34
[mk-app] #1009 Poly%tuple%0. #1008
[mk-app] #1010 = #34 #1009
[mk-app] #1011 => #1007 #1010
[mk-app] #1012 pattern #1007
[mk-quant] #1013 internal_crate__tuple__0_unbox_axiom_definition 1 #1012 #1011
[attach-var-names] #1013 (|x| ; |Poly|)
[mk-app] #1014 not #1007
[mk-app] #1015 or #1014 #1010
[inst-discovered] theory-solving 0 basic# ; #1011
[mk-app] #1016 = #1011 #1015
[instance] 0 #1016
[attach-enode] #1016 0
[end-of-instance]
[mk-quant] #1016 internal_crate__tuple__0_unbox_axiom_definition 1 #1012 #1015
[attach-var-names] #1016 (|x| ; |Poly|)
[mk-app] #1017 has_type #1001 #1006
[mk-app] #1018 pattern #1017
[mk-quant] #1019 internal_crate__tuple__0_has_type_always_definition 1 #1018 #1017
[attach-var-names] #1019 (|x| ; |tuple%0.|)
[mk-app] #1020 tr_bound%core!marker.Tuple. #45 #46
[mk-app] #1021 pattern #1020
[mk-quant] #1022 internal_core__marker__Tuple_trait_type_bounds_definition 2 #1021 #1
[attach-var-names] #1022 (|Self%&| ; |Type|) (|Self%&.| ; |Dcr|)
[mk-var] #1023 3
[mk-app] #1024 tr_bound%core!ops.function.FnOnce. #1023 #264 #45 #46
[mk-app] #1025 sized #45
[mk-app] #1026 proj%%core!ops.function.FnOnce./Output #1023 #264 #45 #46
[mk-app] #1027 sized #1026
[mk-app] #1028 and #1025 #1020 #1027
[mk-app] #1029 => #1024 #1028
[mk-app] #1030 pattern #1024
[mk-quant] #1031 internal_core__ops__function__FnOnce_trait_type_bounds_definition 4 #1030 #1029
[attach-var-names] #1031 (|Args&| ; |Type|) (|Args&.| ; |Dcr|) (|Self%&| ; |Type|) (|Self%&.| ; |Dcr|)
[mk-app] #1032 not #1024
[mk-app] #1033 or #1032 #1028
[inst-discovered] theory-solving 0 basic# ; #1029
[mk-app] #1034 = #1029 #1033
[instance] 0 #1034
[attach-enode] #1034 0
[end-of-instance]
[mk-quant] #1034 internal_core__ops__function__FnOnce_trait_type_bounds_definition 4 #1030 #1033
[attach-var-names] #1034 (|Args&| ; |Type|) (|Args&.| ; |Dcr|) (|Self%&| ; |Type|) (|Self%&.| ; |Dcr|)
[mk-app] #1035 tr_bound%core!ops.function.FnMut. #1023 #264 #45 #46
[mk-app] #1036 and #1024 #1025 #1020
[mk-app] #1037 => #1035 #1036
[mk-app] #1038 pattern #1035
[mk-quant] #1039 internal_core__ops__function__FnMut_trait_type_bounds_definition 4 #1038 #1037
[attach-var-names] #1039 (|Args&| ; |Type|) (|Args&.| ; |Dcr|) (|Self%&| ; |Type|) (|Self%&.| ; |Dcr|)
[mk-app] #1040 not #1035
[mk-app] #1041 or #1040 #1036
[inst-discovered] theory-solving 0 basic# ; #1037
[mk-app] #1042 = #1037 #1041
[instance] 0 #1042
[attach-enode] #1042 0
[end-of-instance]
[mk-quant] #1042 internal_core__ops__function__FnMut_trait_type_bounds_definition 4 #1038 #1041
[attach-var-names] #1042 (|Args&| ; |Type|) (|Args&.| ; |Dcr|) (|Self%&| ; |Type|) (|Self%&.| ; |Dcr|)
[mk-app] #1043 tr_bound%core!ops.function.Fn. #1023 #264 #45 #46
[mk-app] #1044 and #1035 #1025 #1020
[mk-app] #1045 => #1043 #1044
[mk-app] #1046 pattern #1043
[mk-quant] #1047 internal_core__ops__function__Fn_trait_type_bounds_definition 4 #1046 #1045
[attach-var-names] #1047 (|Args&| ; |Type|) (|Args&.| ; |Dcr|) (|Self%&| ; |Type|) (|Self%&.| ; |Dcr|)
[mk-app] #1048 not #1043
[mk-app] #1049 or #1048 #1044
[inst-discovered] theory-solving 0 basic# ; #1045
[mk-app] #1050 = #1045 #1049
[instance] 0 #1050
[attach-enode] #1050 0
[end-of-instance]
[mk-quant] #1050 internal_core__ops__function__Fn_trait_type_bounds_definition 4 #1046 #1049
[attach-var-names] #1050 (|Args&| ; |Type|) (|Args&.| ; |Dcr|) (|Self%&| ; |Type|) (|Self%&.| ; |Dcr|)
[mk-app] #1051 tr_bound%core!alloc.Allocator. #45 #46
[mk-app] #1052 pattern #1051
[mk-quant] #1053 internal_core__alloc__Allocator_trait_type_bounds_definition 2 #1052 #1
[attach-var-names] #1053 (|Self%&| ; |Type|) (|Self%&.| ; |Dcr|)
[mk-app] #1054 sized #1023
[mk-app] #1055 tr_bound%core!marker.Tuple. #1023 #264
[mk-app] #1056 tr_bound%core!ops.function.Fn. #45 #46 #1023 #264
[mk-app] #1057 and #1054 #1055 #1056
[mk-app] #1058 REF #45
[mk-app] #1059 proj%%core!ops.function.FnOnce./Output #1058 #46 #1023 #264
[mk-app] #1060 proj%%core!ops.function.FnOnce./Output #45 #46 #1023 #264
[mk-app] #1061 = #1059 #1060
[mk-app] #1062 => #1057 #1061
[mk-app] #1063 pattern #1059
[mk-quant] #1064 internal_proj____core!ops.function.FnOnce./Output_assoc_type_impl_true_definition 4 #1063 #1062
[attach-var-names] #1064 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #1065 not #1057
[mk-app] #1066 or #1065 #1061
[inst-discovered] theory-solving 0 basic# ; #1062
[mk-app] #1067 = #1062 #1066
[instance] 0 #1067
[attach-enode] #1067 0
[end-of-instance]
[mk-quant] #1067 internal_proj____core!ops.function.FnOnce./Output_assoc_type_impl_true_definition 4 #1063 #1066
[attach-var-names] #1067 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #1068 proj%core!ops.function.FnOnce./Output #1058 #46 #1023 #264
[mk-app] #1069 proj%core!ops.function.FnOnce./Output #45 #46 #1023 #264
[mk-app] #1070 = #1068 #1069
[mk-app] #1071 => #1057 #1070
[mk-app] #1072 pattern #1068
[mk-quant] #1073 internal_proj__core!ops.function.FnOnce./Output_assoc_type_impl_false_definition 4 #1072 #1071
[attach-var-names] #1073 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #1074 or #1065 #1070
[inst-discovered] theory-solving 0 basic# ; #1071
[mk-app] #1075 = #1071 #1074
[instance] 0 #1075
[attach-enode] #1075 0
[end-of-instance]
[mk-quant] #1075 internal_proj__core!ops.function.FnOnce./Output_assoc_type_impl_false_definition 4 #1072 #1074
[attach-var-names] #1075 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #1076 tr_bound%core!ops.function.FnMut. #45 #46 #1023 #264
[mk-app] #1077 and #1054 #1055 #1076
[mk-app] #1078 proj%%core!ops.function.FnOnce./Output #121 #47 #1023 #264
[mk-app] #1079 = #1078 #1060
[mk-app] #1080 => #1077 #1079
[mk-app] #1081 pattern #1078
[mk-quant] #1082 internal_proj____core!ops.function.FnOnce./Output_assoc_type_impl_true_definition 4 #1081 #1080
[attach-var-names] #1082 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #1083 not #1077
[mk-app] #1084 or #1083 #1079
[inst-discovered] theory-solving 0 basic# ; #1080
[mk-app] #1085 = #1080 #1084
[instance] 0 #1085
[attach-enode] #1085 0
[end-of-instance]
[mk-quant] #1085 internal_proj____core!ops.function.FnOnce./Output_assoc_type_impl_true_definition 4 #1081 #1084
[attach-var-names] #1085 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #1086 proj%core!ops.function.FnOnce./Output #121 #47 #1023 #264
[mk-app] #1087 = #1086 #1069
[mk-app] #1088 => #1077 #1087
[mk-app] #1089 pattern #1086
[mk-quant] #1090 internal_proj__core!ops.function.FnOnce./Output_assoc_type_impl_false_definition 4 #1089 #1088
[attach-var-names] #1090 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #1091 or #1083 #1087
[inst-discovered] theory-solving 0 basic# ; #1088
[mk-app] #1092 = #1088 #1091
[instance] 0 #1092
[attach-enode] #1092 0
[end-of-instance]
[mk-quant] #1092 internal_proj__core!ops.function.FnOnce./Output_assoc_type_impl_false_definition 4 #1089 #1091
[attach-var-names] #1092 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-var] #1093 5
[mk-var] #1094 4
[mk-app] #1095 sized #1093
[mk-app] #1096 tr_bound%core!marker.Tuple. #1093 #1094
[mk-app] #1097 tr_bound%core!ops.function.FnOnce. #1023 #264 #1093 #1094
[mk-app] #1098 and #1095 #1025 #1096 #1097 #1051
[mk-app] #1099 BOX #45 #46 #1023
[mk-app] #1100 proj%%core!ops.function.FnOnce./Output #1099 #264 #1093 #1094
[mk-app] #1101 proj%%core!ops.function.FnOnce./Output #1023 #264 #1093 #1094
[mk-app] #1102 = #1100 #1101
[mk-app] #1103 => #1098 #1102
[mk-app] #1104 pattern #1100
[mk-quant] #1105 internal_proj____core!ops.function.FnOnce./Output_assoc_type_impl_true_definition 6 #1104 #1103
[attach-var-names] #1105 (|A&| ; |Type|) (|A&.| ; |Dcr|) (|F&| ; |Type|) (|F&.| ; |Dcr|) (|Args&| ; |Type|) (|Args&.| ; |Dcr|)
[mk-app] #1106 not #1098
[mk-app] #1107 or #1106 #1102
[inst-discovered] theory-solving 0 basic# ; #1103
[mk-app] #1108 = #1103 #1107
[instance] 0 #1108
[attach-enode] #1108 0
[end-of-instance]
[mk-quant] #1108 internal_proj____core!ops.function.FnOnce./Output_assoc_type_impl_true_definition 6 #1104 #1107
[attach-var-names] #1108 (|A&| ; |Type|) (|A&.| ; |Dcr|) (|F&| ; |Type|) (|F&.| ; |Dcr|) (|Args&| ; |Type|) (|Args&.| ; |Dcr|)
[mk-app] #1109 proj%core!ops.function.FnOnce./Output #1099 #264 #1093 #1094
[mk-app] #1110 proj%core!ops.function.FnOnce./Output #1023 #264 #1093 #1094
[mk-app] #1111 = #1109 #1110
[mk-app] #1112 => #1098 #1111
[mk-app] #1113 pattern #1109
[mk-quant] #1114 internal_proj__core!ops.function.FnOnce./Output_assoc_type_impl_false_definition 6 #1113 #1112
[attach-var-names] #1114 (|A&| ; |Type|) (|A&.| ; |Dcr|) (|F&| ; |Type|) (|F&.| ; |Dcr|) (|Args&| ; |Type|) (|Args&.| ; |Dcr|)
[mk-app] #1115 or #1106 #1111
[inst-discovered] theory-solving 0 basic# ; #1112
[mk-app] #1116 = #1112 #1115
[instance] 0 #1116
[attach-enode] #1116 0
[end-of-instance]
[mk-quant] #1116 internal_proj__core!ops.function.FnOnce./Output_assoc_type_impl_false_definition 6 #1113 #1115
[attach-var-names] #1116 (|A&| ; |Type|) (|A&.| ; |Dcr|) (|F&| ; |Type|) (|F&.| ; |Dcr|) (|Args&| ; |Type|) (|Args&.| ; |Dcr|)
[mk-app] #1117 tr_bound%core!ops.function.FnOnce. #121 #47 #1023 #264
[mk-app] #1118 => #1077 #1117
[mk-app] #1119 pattern #1117
[mk-quant] #1120 internal_core__ops__function__impls__impl&__4_trait_impl_definition 4 #1119 #1118
[attach-var-names] #1120 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #1121 or #1083 #1117
[inst-discovered] theory-solving 0 basic# ; #1118
[mk-app] #1122 = #1118 #1121
[instance] 0 #1122
[attach-enode] #1122 0
[end-of-instance]
[mk-quant] #1122 internal_core__ops__function__impls__impl&__4_trait_impl_definition 4 #1119 #1121
[attach-var-names] #1122 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #1123 fuel_bool #792
[mk-app] #1124 MUTREF #1023 #264
[mk-app] #1125 has_type #33 #1124
[mk-app] #1126 has_type #34 #1094
[mk-app] #1127 and #1125 #1126
[mk-app] #1128 and #1095 #1054
[mk-app] #1129 and #1128 #1096
[mk-app] #1130 tr_bound%core!ops.function.FnMut. #1023 #264 #1093 #1094
[mk-app] #1131 and #1129 #1130
[mk-app] #1132 mut_ref_current% #33
[mk-app] #1133 closure_req #264 #1093 #1094 #1132 #34
[mk-app] #1134 and #1131 #1133
[mk-app] #1135 closure_req #1124 #1093 #1094 #33 #34
[mk-app] #1136 => #1134 #1135
[mk-app] #1137 => #1127 #1136
[mk-app] #1138 pattern #1135
[mk-quant] #1139 user_vstd__function__axiom_fn_mut_call_requires_0 6 #1138 #1137
[attach-var-names] #1139 (|args!| ; |Poly|) (|f!| ; |Poly|) (|F&| ; |Type|) (|F&.| ; |Dcr|) (|Args&| ; |Type|) (|Args&.| ; |Dcr|)
[mk-app] #1140 => #1123 #1139
[mk-app] #1141 and #1095 #1054 #1096 #1130 #1133
[mk-app] #1142 not #1141
[mk-app] #1143 or #1142 #1135
[mk-app] #1144 => #1141 #1135
[inst-discovered] theory-solving 0 basic# ; #1144
[mk-app] #1145 = #1144 #1143
[instance] 0 #1145
[attach-enode] #1145 0
[end-of-instance]
[mk-app] #1144 not #1127
[mk-app] #1145 or #1144 #1142 #1135
[mk-app] #1146 => #1127 #1143
[inst-discovered] theory-solving 0 basic# ; #1146
[mk-app] #1147 = #1146 #1145
[instance] 0 #1147
[attach-enode] #1147 0
[end-of-instance]
[mk-quant] #1143 user_vstd__function__axiom_fn_mut_call_requires_0 6 #1138 #1145
[attach-var-names] #1143 (|args!| ; |Poly|) (|f!| ; |Poly|) (|F&| ; |Type|) (|F&.| ; |Dcr|) (|Args&| ; |Type|) (|Args&.| ; |Dcr|)
[mk-app] #1146 not #1123
[mk-app] #1147 or #1146 #1143
[mk-app] #1148 => #1123 #1143
[inst-discovered] theory-solving 0 basic# ; #1148
[mk-app] #1149 = #1148 #1147
[instance] 0 #1149
[attach-enode] #1149 0
[end-of-instance]
[mk-app] #1148 fuel_bool #793
[mk-var] #1149 6
[mk-var] #1150 5
[mk-var] #1151 4
[mk-var] #1152 3
[mk-app] #1153 MUTREF #1151 #1152
[mk-app] #1154 has_type #44 #1153
[mk-app] #1155 has_type #33 #1150
[mk-app] #1156 proj%core!ops.function.FnOnce./Output #1151 #1152 #1149 #1150
[mk-app] #1157 has_type #34 #1156
[mk-app] #1158 and #1154 #1155 #1157
[mk-app] #1159 sized #1149
[mk-app] #1160 sized #1151
[mk-app] #1161 and #1159 #1160
[mk-app] #1162 tr_bound%core!marker.Tuple. #1149 #1150
[mk-app] #1163 and #1161 #1162
[mk-app] #1164 tr_bound%core!ops.function.FnMut. #1151 #1152 #1149 #1150
[mk-app] #1165 and #1163 #1164
[mk-app] #1166 closure_ens #1153 #1149 #1150 #44 #33 #34
[mk-app] #1167 and #1165 #1166
[mk-app] #1168 closure_ens #1152 #1149 #1150 #49 #33 #34
[mk-app] #1169 = #49 #57
[mk-app] #1170 and #1168 #1169
[mk-app] #1171 => #1167 #1170
[mk-app] #1172 => #1158 #1171
[mk-app] #1173 pattern #1166
[mk-quant] #1174 user_vstd__function__axiom_fn_mut_call_ensures_1 7 #1173 #1172
[attach-var-names] #1174 (|output!| ; |Poly|) (|args!| ; |Poly|) (|f!| ; |Poly|) (|F&| ; |Type|) (|F&.| ; |Dcr|) (|Args&| ; |Type|) (|Args&.| ; |Dcr|)
[mk-app] #1175 => #1148 #1174
[mk-app] #1176 and #1159 #1160 #1162 #1164 #1166
[mk-app] #1177 not #1176
[mk-app] #1178 or #1177 #1170
[mk-app] #1179 => #1176 #1170
[inst-discovered] theory-solving 0 basic# ; #1179
[mk-app] #1180 = #1179 #1178
[instance] 0 #1180
[attach-enode] #1180 0
[end-of-instance]
[mk-app] #1179 not #1158
[mk-app] #1180 or #1179 #1177 #1170
[mk-app] #1181 => #1158 #1178
[inst-discovered] theory-solving 0 basic# ; #1181
[mk-app] #1182 = #1181 #1180
[instance] 0 #1182
[attach-enode] #1182 0
[end-of-instance]
[mk-quant] #1178 user_vstd__function__axiom_fn_mut_call_ensures_1 7 #1173 #1180
[attach-var-names] #1178 (|output!| ; |Poly|) (|args!| ; |Poly|) (|f!| ; |Poly|) (|F&| ; |Type|) (|F&.| ; |Dcr|) (|Args&| ; |Type|) (|Args&.| ; |Dcr|)
[mk-app] #1181 not #1148
[mk-app] #1182 or #1181 #1178
[mk-app] #1183 => #1148 #1178
[inst-discovered] theory-solving 0 basic# ; #1183
[mk-app] #1184 = #1183 #1182
[instance] 0 #1184
[attach-enode] #1184 0
[end-of-instance]
[mk-app] #1183 tr_bound%core!marker.Tuple. #121 #1006
[mk-app] #1184 fuel_bool_default #794
[mk-var] #1185 0
[mk-app] #1186 the_q!model.rec%pow2.? #33 #1185
[mk-app] #1187 zero
[mk-app] #1188 the_q!model.rec%pow2.? #33 #1187
[mk-app] #1189 = #1186 #1188
[mk-app] #1190 pattern #1186
[mk-quant] #1191 internal_the_q!model.pow2._fuel_to_zero_definition 2 #1190 #1189
[attach-var-names] #1191 (|fuel%| ; |Fuel|) (|n!| ; |Poly|)
[mk-app] #1192 has_type #33 #196
[mk-app] #1193 succ #1185
[mk-app] #1194 the_q!model.rec%pow2.? #33 #1193
[mk-app] #1195 = #672 #337
[mk-app] #1196 Int
[attach-meaning] #1196 arith 2
[mk-app] #1197 Sub #672 #292
[mk-app] #1198 nClip #1197
[mk-app] #1199 I #1198
[mk-app] #1200 the_q!model.rec%pow2.? #1199 #1185
[mk-app] #1201 Mul #1196 #1200
[mk-app] #1202 if #1195 #292 #1201
[mk-app] #1203 = #1194 #1202
[mk-app] #1204 => #1192 #1203
[mk-app] #1205 pattern #1194
[mk-quant] #1206 internal_the_q!model.pow2._fuel_to_body_definition 2 #1205 #1204
[attach-var-names] #1206 (|fuel%| ; |Fuel|) (|n!| ; |Poly|)
[mk-app] #1207 not #1192
[mk-app] #1208 or #1207 #1203
[inst-discovered] theory-solving 0 basic# ; #1204
[mk-app] #1209 = #1204 #1208
[instance] 0 #1209
[attach-enode] #1209 0
[end-of-instance]
[mk-quant] #1209 internal_the_q!model.pow2._fuel_to_body_definition 2 #1205 #1208
[attach-var-names] #1209 (|fuel%| ; |Fuel|) (|n!| ; |Poly|)
[mk-app] #1210 fuel_bool #794
[mk-app] #1211 the_q!model.pow2.? #34
[mk-app] #1212 fuel_nat%the_q!model.pow2.
[mk-app] #1213 succ #1212
[mk-app] #1214 the_q!model.rec%pow2.? #34 #1213
[mk-app] #1215 = #1211 #1214
[mk-app] #1216 => #197 #1215
[mk-app] #1217 pattern #1211
[mk-quant] #1218 internal_the_q!model.pow2.?_definition 1 #1217 #1216
[attach-var-names] #1218 (|n!| ; |Poly|)
[mk-app] #1219 => #1210 #1218
[mk-app] #1220 or #201 #1215
[inst-discovered] theory-solving 0 basic# ; #1216
[mk-app] #1221 = #1216 #1220
[instance] 0 #1221
[attach-enode] #1221 0
[end-of-instance]
[mk-quant] #1221 internal_the_q!model.pow2.?_definition 1 #1217 #1220
[attach-var-names] #1221 (|n!| ; |Poly|)
[mk-app] #1222 not #1210
[mk-app] #1223 or #1222 #1221
[mk-app] #1224 => #1210 #1221
[inst-discovered] theory-solving 0 basic# ; #1224
[mk-app] #1225 = #1224 #1223
[instance] 0 #1225
[attach-enode] #1225 0
[end-of-instance]
[mk-app] #1224 fuel_bool_default #795
[mk-app] #1225 fuel_bool #795
[mk-app] #1226 the_q!model.abs_int.? #34
[mk-app] #1227 Sub #337 #187
[mk-app] #1228 if #517 #187 #1227
[mk-app] #1229 = #1226 #1228
[mk-app] #1230 pattern #1226
[mk-quant] #1231 internal_the_q!model.abs_int.?_definition 1 #1230 #1229
[attach-var-names] #1231 (|x!| ; |Poly|)
[mk-app] #1232 => #1225 #1231
[mk-app] #1233 not #1225
[mk-app] #1234 or #1233 #1231
[inst-discovered] theory-solving 0 basic# ; #1232
[mk-app] #1235 = #1232 #1234
[instance] 0 #1235
[attach-enode] #1235 0
[end-of-instance]
[mk-app] #1235 fuel_bool_default #796
[mk-app] #1236 fuel_bool #796
[mk-app] #1237 the_q!model.max_int.? #33 #34
[mk-app] #1238 >= #672 #187
[mk-app] #1239 if #1238 #33 #34
[mk-app] #1240 %I #1239
[mk-app] #1241 = #1237 #1240
[mk-app] #1242 pattern #1237
[mk-quant] #1243 internal_the_q!model.max_int.?_definition 2 #1242 #1241
[attach-var-names] #1243 (|b!| ; |Poly|) (|a!| ; |Poly|)
[mk-app] #1244 => #1236 #1243
[attach-meaning] #366 arith (- 1)
[mk-app] #1245 * #366 #187
[mk-app] #1246 + #1245 #672
[attach-meaning] #366 arith (- 1)
[mk-app] #1247 * #366 #672
[mk-app] #1248 + #187 #1247
[mk-app] #1245 <= #1248 #337
[inst-discovered] theory-solving 0 arith# ; #1238
[mk-app] #1246 = #1238 #1245
[instance] 0 #1246
[attach-enode] #1246 0
[end-of-instance]
[mk-app] #1246 if #1245 #33 #34
[mk-app] #1249 %I #1246
[mk-app] #1250 = #1237 #1249
[mk-quant] #1251 internal_the_q!model.max_int.?_definition 2 #1242 #1250
[attach-var-names] #1251 (|b!| ; |Poly|) (|a!| ; |Poly|)
[mk-app] #1252 not #1236
[mk-app] #1253 or #1252 #1251
[mk-app] #1254 => #1236 #1251
[inst-discovered] theory-solving 0 basic# ; #1254
[mk-app] #1255 = #1254 #1253
[instance] 0 #1255
[attach-enode] #1255 0
[end-of-instance]
[mk-app] #1254 fuel_bool_default #797
[mk-app] #1255 fuel_bool #797
[mk-app] #1256 the_q!model.divides.? #33 #34
[mk-app] #1257 Mul #662 #123
[mk-app] #1258 = #672 #1257
[mk-app] #1259 pattern #1257
[mk-quant] #1260 user_the_q__model__divides_2 1 #1259 #1258
[attach-var-names] #1260 (|k$| ; |Int|)
[mk-app] #1261 = #1256 #1260
[mk-app] #1262 pattern #1256
[mk-quant] #1263 internal_the_q!model.divides.?_definition 2 #1262 #1261
[attach-var-names] #1263 (|n!| ; |Poly|) (|d!| ; |Poly|)
[mk-app] #1264 => #1255 #1263
[mk-app] #1265 not #1255
[mk-app] #1266 or #1265 #1263
[inst-discovered] theory-solving 0 basic# ; #1264
[mk-app] #1267 = #1264 #1266
[instance] 0 #1267
[attach-enode] #1267 0
[end-of-instance]
[mk-app] #1267 fuel_bool_default #798
[mk-app] #1268 the_q!model.rec%gcd_nat.? #44 #33 #1185
[mk-app] #1269 the_q!model.rec%gcd_nat.? #44 #33 #1187
[mk-app] #1270 = #1268 #1269
[mk-app] #1271 pattern #1268
[mk-quant] #1272 internal_the_q!model.gcd_nat._fuel_to_zero_definition 3 #1271 #1270
[attach-var-names] #1272 (|fuel%| ; |Fuel|) (|b!| ; |Poly|) (|a!| ; |Poly|)
[mk-app] #1273 has_type #44 #196
[mk-app] #1274 and #1273 #1192
[mk-app] #1275 the_q!model.rec%gcd_nat.? #44 #33 #1193
[mk-app] #1276 EucMod #662 #672
[mk-app] #1277 I #1276
[mk-app] #1278 the_q!model.rec%gcd_nat.? #33 #1277 #1185
[mk-app] #1279 if #1195 #662 #1278
[mk-app] #1280 = #1275 #1279
[mk-app] #1281 => #1274 #1280
[mk-app] #1282 pattern #1275
[mk-quant] #1283 internal_the_q!model.gcd_nat._fuel_to_body_definition 3 #1282 #1281
[attach-var-names] #1283 (|fuel%| ; |Fuel|) (|b!| ; |Poly|) (|a!| ; |Poly|)
[mk-app] #1284 not #1274
[mk-app] #1285 or #1284 #1280
[inst-discovered] theory-solving 0 basic# ; #1281
[mk-app] #1286 = #1281 #1285
[instance] 0 #1286
[attach-enode] #1286 0
[end-of-instance]
[mk-quant] #1286 internal_the_q!model.gcd_nat._fuel_to_body_definition 3 #1282 #1285
[attach-var-names] #1286 (|fuel%| ; |Fuel|) (|b!| ; |Poly|) (|a!| ; |Poly|)
[mk-app] #1287 fuel_bool #798
[mk-app] #1288 and #1192 #197
[mk-app] #1289 the_q!model.gcd_nat.? #33 #34
[mk-app] #1290 fuel_nat%the_q!model.gcd_nat.
[mk-app] #1291 succ #1290
[mk-app] #1292 the_q!model.rec%gcd_nat.? #33 #34 #1291
[mk-app] #1293 = #1289 #1292
[mk-app] #1294 => #1288 #1293
[mk-app] #1295 pattern #1289
[mk-quant] #1296 internal_the_q!model.gcd_nat.?_definition 2 #1295 #1294
[attach-var-names] #1296 (|b!| ; |Poly|) (|a!| ; |Poly|)
[mk-app] #1297 => #1287 #1296
[mk-app] #1298 not #1288
[mk-app] #1299 or #1298 #1293
[inst-discovered] theory-solving 0 basic# ; #1294
[mk-app] #1300 = #1294 #1299
[instance] 0 #1300
[attach-enode] #1300 0
[end-of-instance]
[mk-quant] #1300 internal_the_q!model.gcd_nat.?_definition 2 #1295 #1299
[attach-var-names] #1300 (|b!| ; |Poly|) (|a!| ; |Poly|)
[mk-app] #1301 not #1287
[mk-app] #1302 or #1301 #1300
[mk-app] #1303 => #1287 #1300
[inst-discovered] theory-solving 0 basic# ; #1303
[mk-app] #1304 = #1303 #1302
[instance] 0 #1304
[attach-enode] #1304 0
[end-of-instance]
[mk-app] #1303 <= #337 #1289
[mk-app] #1304 => #1288 #1303
[mk-quant] #1305 internal_the_q!model.gcd_nat.?_pre_post_definition 2 #1295 #1304
[attach-var-names] #1305 (|b!| ; |Poly|) (|a!| ; |Poly|)
[attach-meaning] #366 arith (- 1)
[mk-app] #1306 * #366 #1289
[mk-app] #1307 >= #1289 #337
[inst-discovered] theory-solving 0 arith# ; #1303
[mk-app] #1306 = #1303 #1307
[instance] 0 #1306
[attach-enode] #1306 0
[end-of-instance]
[mk-app] #1306 or #1298 #1307
[mk-app] #1308 => #1288 #1307
[inst-discovered] theory-solving 0 basic# ; #1308
[mk-app] #1309 = #1308 #1306
[instance] 0 #1309
[attach-enode] #1309 0
[end-of-instance]
[mk-quant] #1308 internal_the_q!model.gcd_nat.?_pre_post_definition 2 #1295 #1306
[attach-var-names] #1308 (|b!| ; |Poly|) (|a!| ; |Poly|)
[mk-app] #1309 <= #337 #1268
[mk-app] #1310 => #1274 #1309
[mk-quant] #1311 internal_the_q!model.rec__gcd_nat.?_pre_post_rec_definition 3 #1271 #1310
[attach-var-names] #1311 (|fuel%| ; |Fuel|) (|b!| ; |Poly|) (|a!| ; |Poly|)
[attach-meaning] #366 arith (- 1)
[mk-app] #1312 * #366 #1268
[mk-app] #1313 >= #1268 #337
[inst-discovered] theory-solving 0 arith# ; #1309
[mk-app] #1312 = #1309 #1313
[instance] 0 #1312
[attach-enode] #1312 0
[end-of-instance]
[mk-app] #1312 or #1284 #1313
[mk-app] #1314 => #1274 #1313
[inst-discovered] theory-solving 0 basic# ; #1314
[mk-app] #1315 = #1314 #1312
[instance] 0 #1315
[attach-enode] #1315 0
[end-of-instance]
[mk-quant] #1314 internal_the_q!model.rec__gcd_nat.?_pre_post_rec_definition 3 #1271 #1312
[attach-var-names] #1314 (|fuel%| ; |Fuel|) (|b!| ; |Poly|) (|a!| ; |Poly|)
[mk-app] #1315 fuel_bool_default #799
[mk-app] #1316 fuel_bool #799
[mk-app] #1317 the_q!model.gcd_int.? #33 #34
[mk-app] #1318 the_q!model.abs_int.? #33
[mk-app] #1319 nClip #1318
[mk-app] #1320 I #1319
[mk-app] #1321 nClip #1226
[mk-app] #1322 I #1321
[mk-app] #1323 the_q!model.gcd_nat.? #1320 #1322
[mk-app] #1324 = #1317 #1323
[mk-app] #1325 pattern #1317
[mk-quant] #1326 internal_the_q!model.gcd_int.?_definition 2 #1325 #1324
[attach-var-names] #1326 (|b!| ; |Poly|) (|a!| ; |Poly|)
[mk-app] #1327 => #1316 #1326
[mk-app] #1328 not #1316
[mk-app] #1329 or #1328 #1326
[inst-discovered] theory-solving 0 basic# ; #1327
[mk-app] #1330 = #1327 #1329
[instance] 0 #1330
[attach-enode] #1330 0
[end-of-instance]
[mk-app] #1330 fuel_bool_default #800
[mk-app] #1331 the_q!model.rec%bitlen.? #33 #1185
[mk-app] #1332 the_q!model.rec%bitlen.? #33 #1187
[mk-app] #1333 = #1331 #1332
[mk-app] #1334 pattern #1331
[mk-quant] #1335 internal_the_q!model.bitlen._fuel_to_zero_definition 2 #1334 #1333
[attach-var-names] #1335 (|fuel%| ; |Fuel|) (|x!| ; |Poly|)
[mk-app] #1336 has_type #33 #185
[mk-app] #1337 the_q!model.rec%bitlen.? #33 #1193
[mk-app] #1338 <= #672 #337
[mk-app] #1339 EucDiv #672 #1196
[mk-app] #1340 I #1339
[mk-app] #1341 the_q!model.rec%bitlen.? #1340 #1185
[mk-app] #1342 Add #1341 #292
[mk-app] #1343 nClip #1342
[mk-app] #1344 if #1338 #337 #1343
[mk-app] #1345 = #1337 #1344
[mk-app] #1346 => #1336 #1345
[mk-app] #1347 pattern #1337
[mk-quant] #1348 internal_the_q!model.bitlen._fuel_to_body_definition 2 #1347 #1346
[attach-var-names] #1348 (|fuel%| ; |Fuel|) (|x!| ; |Poly|)
[mk-app] #1349 not #1336
[mk-app] #1350 or #1349 #1345
[inst-discovered] theory-solving 0 basic# ; #1346
[mk-app] #1351 = #1346 #1350
[instance] 0 #1351
[attach-enode] #1351 0
[end-of-instance]
[mk-quant] #1351 internal_the_q!model.bitlen._fuel_to_body_definition 2 #1347 #1350
[attach-var-names] #1351 (|fuel%| ; |Fuel|) (|x!| ; |Poly|)
[mk-app] #1352 fuel_bool #800
[mk-app] #1353 the_q!model.bitlen.? #34
[mk-app] #1354 fuel_nat%the_q!model.bitlen.
[mk-app] #1355 succ #1354
[mk-app] #1356 the_q!model.rec%bitlen.? #34 #1355
[mk-app] #1357 = #1353 #1356
[mk-app] #1358 => #186 #1357
[mk-app] #1359 pattern #1353
[mk-quant] #1360 internal_the_q!model.bitlen.?_definition 1 #1359 #1358
[attach-var-names] #1360 (|x!| ; |Poly|)
[mk-app] #1361 => #1352 #1360
[mk-app] #1362 or #193 #1357
[inst-discovered] theory-solving 0 basic# ; #1358
[mk-app] #1363 = #1358 #1362
[instance] 0 #1363
[attach-enode] #1363 0
[end-of-instance]
[mk-quant] #1363 internal_the_q!model.bitlen.?_definition 1 #1359 #1362
[attach-var-names] #1363 (|x!| ; |Poly|)
[mk-app] #1364 not #1352
[mk-app] #1365 or #1364 #1363
[mk-app] #1366 => #1352 #1363
[inst-discovered] theory-solving 0 basic# ; #1366
[mk-app] #1367 = #1366 #1365
[instance] 0 #1367
[attach-enode] #1367 0
[end-of-instance]
[mk-app] #1366 <= #337 #1353
[mk-app] #1367 => #186 #1366
[mk-quant] #1368 internal_the_q!model.bitlen.?_pre_post_definition 1 #1359 #1367
[attach-var-names] #1368 (|x!| ; |Poly|)
[attach-meaning] #366 arith (- 1)
[mk-app] #1369 * #366 #1353
[mk-app] #1370 >= #1353 #337
[inst-discovered] theory-solving 0 arith# ; #1366
[mk-app] #1369 = #1366 #1370
[instance] 0 #1369
[attach-enode] #1369 0
[end-of-instance]
[mk-app] #1369 or #193 #1370
[mk-app] #1371 => #186 #1370
[inst-discovered] theory-solving 0 basic# ; #1371
[mk-app] #1372 = #1371 #1369
[instance] 0 #1372
[attach-enode] #1372 0
[end-of-instance]
[mk-quant] #1371 internal_the_q!model.bitlen.?_pre_post_definition 1 #1359 #1369
[attach-var-names] #1371 (|x!| ; |Poly|)
[mk-app] #1372 <= #337 #1331
[mk-app] #1373 => #1336 #1372
[mk-quant] #1374 internal_the_q!model.rec__bitlen.?_pre_post_rec_definition 2 #1334 #1373
[attach-var-names] #1374 (|fuel%| ; |Fuel|) (|x!| ; |Poly|)
[attach-meaning] #366 arith (- 1)
[mk-app] #1375 * #366 #1331
[mk-app] #1376 >= #1331 #337
[inst-discovered] theory-solving 0 arith# ; #1372
[mk-app] #1375 = #1372 #1376
[instance] 0 #1375
[attach-enode] #1375 0
[end-of-instance]
[mk-app] #1375 or #1349 #1376
[mk-app] #1377 => #1336 #1376
[inst-discovered] theory-solving 0 basic# ; #1377
[mk-app] #1378 = #1377 #1375
[instance] 0 #1378
[attach-enode] #1378 0
[end-of-instance]
[mk-quant] #1377 internal_the_q!model.rec__bitlen.?_pre_post_rec_definition 2 #1334 #1375
[attach-var-names] #1377 (|fuel%| ; |Fuel|) (|x!| ; |Poly|)
[mk-app] #1378 fuel_bool_default #817
[mk-app] #1379 fuel_bool #817
[mk-app] #1380 the_q!types.MAX_MAG.?
[mk-app] #1381 Int
[attach-meaning] #1381 arith 4611686018427387903
[mk-app] #1382 = #1380 #1381
[mk-app] #1383 => #1379 #1382
[mk-app] #1384 not #1379
[mk-app] #1385 or #1384 #1382
[inst-discovered] theory-solving 0 basic# ; #1383
[mk-app] #1386 = #1383 #1385
[instance] 0 #1386
[attach-enode] #1386 0
[end-of-instance]
[attach-meaning] #273 arith 64
[mk-app] #1386 iInv #273 #1380
[mk-app] #1387 fuel_bool_default #801
[mk-app] #1388 fuel_bool #801
[mk-app] #1389 the_q!model.max_mag.? #34
[mk-app] #1390 = #1389 #1380
[mk-app] #1391 pattern #1389
[mk-quant] #1392 internal_the_q!model.max_mag.?_definition 1 #1391 #1390
[attach-var-names] #1392 (|no%param| ; |Poly|)
[mk-app] #1393 => #1388 #1392
[mk-app] #1394 not #1388
[mk-app] #1395 or #1394 #1392
[inst-discovered] theory-solving 0 basic# ; #1393
[mk-app] #1396 = #1393 #1395
[instance] 0 #1396
[attach-enode] #1396 0
[end-of-instance]
[mk-app] #1396 fuel_bool_default #802
[mk-app] #1397 fuel_bool #802
[mk-app] #1398 the_q!model.fits_budget.? #33 #34
[mk-app] #1399 I #337
[mk-app] #1400 the_q!model.max_mag.? #1399
[mk-app] #1401 <= #1318 #1400
[mk-app] #1402 <= #187 #1400
[mk-app] #1403 and #1401 #1402
[mk-app] #1404 = #1398 #1403
[mk-app] #1405 pattern #1398
[mk-quant] #1406 internal_the_q!model.fits_budget.?_definition 2 #1405 #1404
[attach-var-names] #1406 (|d!| ; |Poly|) (|n!| ; |Poly|)
[mk-app] #1407 => #1397 #1406
[attach-meaning] #366 arith (- 1)
[mk-app] #1408 * #366 #1400
[mk-app] #1409 + #1318 #1408
[mk-app] #1410 <= #1409 #337
[inst-discovered] theory-solving 0 arith# ; #1401
[mk-app] #1411 = #1401 #1410
[instance] 0 #1411
[attach-enode] #1411 0
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #1411 + #187 #1408
[mk-app] #1412 <= #1411 #337
[inst-discovered] theory-solving 0 arith# ; #1402
[mk-app] #1413 = #1402 #1412
[instance] 0 #1413
[attach-enode] #1413 0
[end-of-instance]
[mk-app] #1413 and #1410 #1412
[mk-app] #1414 = #1398 #1413
[mk-quant] #1415 internal_the_q!model.fits_budget.?_definition 2 #1405 #1414
[attach-var-names] #1415 (|d!| ; |Poly|) (|n!| ; |Poly|)
[mk-app] #1416 not #1397
[mk-app] #1417 or #1416 #1415
[mk-app] #1418 => #1397 #1415
[inst-discovered] theory-solving 0 basic# ; #1418
[mk-app] #1419 = #1418 #1417
[instance] 0 #1419
[attach-enode] #1419 0
[end-of-instance]
[mk-app] #1418 fuel_bool_default #803
[mk-app] #1419 fuel_bool #803
[mk-app] #1420 the_q!model.magnitude_fits.? #33 #34
[mk-app] #1421 Mul #1400 #187
[mk-app] #1422 <= #1318 #1421
[mk-app] #1423 = #1420 #1422
[mk-app] #1424 pattern #1420
[mk-quant] #1425 internal_the_q!model.magnitude_fits.?_definition 2 #1424 #1423
[attach-var-names] #1425 (|d!| ; |Poly|) (|n!| ; |Poly|)
[mk-app] #1426 => #1419 #1425
[attach-meaning] #366 arith (- 1)
[mk-app] #1427 * #366 #1421
[mk-app] #1428 + #1318 #1427
[mk-app] #1429 <= #1428 #337
[inst-discovered] theory-solving 0 arith# ; #1422
[mk-app] #1430 = #1422 #1429
[instance] 0 #1430
[attach-enode] #1430 0
[end-of-instance]
[mk-app] #1430 = #1420 #1429
[mk-quant] #1431 internal_the_q!model.magnitude_fits.?_definition 2 #1424 #1430
[attach-var-names] #1431 (|d!| ; |Poly|) (|n!| ; |Poly|)
[mk-app] #1432 not #1419
[mk-app] #1433 or #1432 #1431
[mk-app] #1434 => #1419 #1431
[inst-discovered] theory-solving 0 basic# ; #1434
[mk-app] #1435 = #1434 #1433
[instance] 0 #1435
[attach-enode] #1435 0
[end-of-instance]
[mk-app] #1434 fuel_bool_default #804
[mk-app] #1435 fuel_bool #804
[mk-app] #1436 the_q!model.impl&%0.wf.? #34
[mk-app] #1437 > #993 #337
[mk-app] #1438 I #981
[mk-app] #1439 I #993
[mk-app] #1440 the_q!model.gcd_int.? #1438 #1439
[mk-app] #1441 = #1440 #292
[mk-app] #1442 and #1437 #1441
[mk-app] #1443 = #981 #337
[mk-app] #1444 = #993 #292
[mk-app] #1445 => #1443 #1444
[mk-app] #1446 and #1442 #1445
[mk-app] #1447 the_q!model.abs_int.? #1438
[mk-app] #1448 <= #1447 #1400
[mk-app] #1449 and #1446 #1448
[mk-app] #1450 <= #993 #1400
[mk-app] #1451 and #1449 #1450
[mk-app] #1452 = #1436 #1451
[mk-app] #1453 pattern #1436
[mk-quant] #1454 internal_the_q!model.impl&__0.wf.?_definition 1 #1453 #1452
[attach-var-names] #1454 (|self!| ; |Poly|)
[mk-app] #1455 => #1435 #1454
[mk-app] #1456 <= #993 #337
[mk-app] #1457 not #1456
[inst-discovered] theory-solving 0 arith# ; #1437
[mk-app] #1458 = #1437 #1457
[instance] 0 #1458
[attach-enode] #1458 0
[end-of-instance]
[mk-app] #1458 not #1443
[mk-app] #1459 or #1458 #1444
[inst-discovered] theory-solving 0 basic# ; #1445
[mk-app] #1460 = #1445 #1459
[instance] 0 #1460
[attach-enode] #1460 0
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #1460 + #1408 #1447
[attach-meaning] #366 arith (- 1)
[mk-app] #1461 * #366 #1447
[mk-app] #1462 + #1400 #1461
[mk-app] #1460 >= #1462 #337
[inst-discovered] theory-solving 0 arith# ; #1448
[mk-app] #1463 = #1448 #1460
[instance] 0 #1463
[attach-enode] #1463 0
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #1463 + #993 #1408
[mk-app] #1464 <= #1463 #337
[inst-discovered] theory-solving 0 arith# ; #1450
[mk-app] #1465 = #1450 #1464
[instance] 0 #1465
[attach-enode] #1465 0
[end-of-instance]
[mk-app] #1465 and #1457 #1441 #1459 #1460 #1464
[mk-app] #1466 = #1436 #1465
[mk-quant] #1467 internal_the_q!model.impl&__0.wf.?_definition 1 #1453 #1466
[attach-var-names] #1467 (|self!| ; |Poly|)
[mk-app] #1468 not #1435
[mk-app] #1469 or #1468 #1467
[mk-app] #1470 => #1435 #1467
[inst-discovered] theory-solving 0 basic# ; #1470
[mk-app] #1471 = #1470 #1469
[instance] 0 #1471
[attach-enode] #1471 0
[end-of-instance]
[mk-app] #1470 fuel_bool_default #805
[mk-app] #1471 fuel_bool #805
[mk-app] #1472 the_q!model.impl&%0.n.? #34
[mk-app] #1473 = #1472 #981
[mk-app] #1474 pattern #1472
[mk-quant] #1475 internal_the_q!model.impl&__0.n.?_definition 1 #1474 #1473
[attach-var-names] #1475 (|self!| ; |Poly|)
[mk-app] #1476 => #1471 #1475
[mk-app] #1477 not #1471
[mk-app] #1478 or #1477 #1475
[inst-discovered] theory-solving 0 basic# ; #1476
[mk-app] #1479 = #1476 #1478
[instance] 0 #1479
[attach-enode] #1479 0
[end-of-instance]
[mk-app] #1479 fuel_bool_default #806
[mk-app] #1480 fuel_bool #806
[mk-app] #1481 the_q!model.impl&%0.d.? #34
[mk-app] #1482 = #1481 #993
[mk-app] #1483 pattern #1481
[mk-quant] #1484 internal_the_q!model.impl&__0.d.?_definition 1 #1483 #1482
[attach-var-names] #1484 (|self!| ; |Poly|)
[mk-app] #1485 => #1480 #1484
[mk-app] #1486 not #1480
[mk-app] #1487 or #1486 #1484
[inst-discovered] theory-solving 0 basic# ; #1485
[mk-app] #1488 = #1485 #1487
[instance] 0 #1488
[attach-enode] #1488 0
[end-of-instance]
[mk-app] #1488 fuel_bool_default #807
[mk-app] #1489 fuel_bool #807
[mk-app] #1490 the_q!model.q_eq.? #33 #34
[mk-app] #1491 the_q!model.impl&%0.n.? #33
[mk-app] #1492 Mul #1491 #1481
[mk-app] #1493 the_q!model.impl&%0.d.? #33
[mk-app] #1494 Mul #1472 #1493
[mk-app] #1495 = #1492 #1494
[mk-app] #1496 = #1490 #1495
[mk-app] #1497 pattern #1490
[mk-quant] #1498 internal_the_q!model.q_eq.?_definition 2 #1497 #1496
[attach-var-names] #1498 (|b!| ; |Poly|) (|a!| ; |Poly|)
[mk-app] #1499 => #1489 #1498
[mk-app] #1500 not #1489
[mk-app] #1501 or #1500 #1498
[inst-discovered] theory-solving 0 basic# ; #1499
[mk-app] #1502 = #1499 #1501
[instance] 0 #1502
[attach-enode] #1502 0
[end-of-instance]
[mk-app] #1502 fuel_bool_default #808
[mk-app] #1503 fuel_bool #808
[mk-app] #1504 the_q!model.q_le.? #33 #34
[mk-app] #1505 <= #1492 #1494
[mk-app] #1506 = #1504 #1505
[mk-app] #1507 pattern #1504
[mk-quant] #1508 internal_the_q!model.q_le.?_definition 2 #1507 #1506
[attach-var-names] #1508 (|b!| ; |Poly|) (|a!| ; |Poly|)
[mk-app] #1509 => #1503 #1508
[attach-meaning] #366 arith (- 1)
[mk-app] #1510 * #366 #1494
[mk-app] #1511 + #1492 #1510
[mk-app] #1512 <= #1511 #337
[inst-discovered] theory-solving 0 arith# ; #1505
[mk-app] #1513 = #1505 #1512
[instance] 0 #1513
[attach-enode] #1513 0
[end-of-instance]
[mk-app] #1513 = #1504 #1512
[mk-quant] #1514 internal_the_q!model.q_le.?_definition 2 #1507 #1513
[attach-var-names] #1514 (|b!| ; |Poly|) (|a!| ; |Poly|)
[mk-app] #1515 not #1503
[mk-app] #1516 or #1515 #1514
[mk-app] #1517 => #1503 #1514
[inst-discovered] theory-solving 0 basic# ; #1517
[mk-app] #1518 = #1517 #1516
[instance] 0 #1518
[attach-enode] #1518 0
[end-of-instance]
[mk-app] #1517 fuel_bool_default #809
[mk-app] #1518 fuel_bool #809
[mk-app] #1519 the_q!model.q_lt.? #33 #34
[mk-app] #1520 < #1492 #1494
[mk-app] #1521 = #1519 #1520
[mk-app] #1522 pattern #1519
[mk-quant] #1523 internal_the_q!model.q_lt.?_definition 2 #1522 #1521
[attach-var-names] #1523 (|b!| ; |Poly|) (|a!| ; |Poly|)
[mk-app] #1524 => #1518 #1523
[mk-app] #1525 <= #1494 #1492
[mk-app] #1526 not #1525
[inst-discovered] theory-solving 0 arith# ; #1520
[mk-app] #1527 = #1520 #1526
[instance] 0 #1527
[attach-enode] #1527 0
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #1527 * #366 #1492
[mk-app] #1528 + #1527 #1494
[attach-meaning] #366 arith (- 1)
[mk-app] #1527 >= #1511 #337
[inst-discovered] theory-solving 0 arith# ; #1525
[mk-app] #1528 = #1525 #1527
[instance] 0 #1528
[attach-enode] #1528 0
[end-of-instance]
[mk-app] #1528 not #1527
[mk-app] #1529 = #1527 #1519
[mk-app] #1530 not #1529
[mk-app] #1531 = #1519 #1528
[inst-discovered] theory-solving 0 basic# ; #1531
[mk-app] #1532 = #1531 #1530
[instance] 0 #1532
[attach-enode] #1532 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1530
[mk-app] #1531 = #1530 #1530
[instance] 0 #1531
[attach-enode] #1531 0
[end-of-instance]
[mk-quant] #1531 internal_the_q!model.q_lt.?_definition 2 #1522 #1530
[attach-var-names] #1531 (|b!| ; |Poly|) (|a!| ; |Poly|)
[mk-app] #1528 not #1518
[mk-app] #1525 or #1528 #1531
[mk-app] #1526 => #1518 #1531
[inst-discovered] theory-solving 0 basic# ; #1526
[mk-app] #1532 = #1526 #1525
[instance] 0 #1532
[attach-enode] #1532 0
[end-of-instance]
[mk-app] #1526 fuel_bool_default #810
[mk-app] #1532 fuel_bool #810
[mk-app] #1533 the_q!model.q_is.? #44 #33 #34
[mk-app] #1534 the_q!model.impl&%0.n.? #44
[mk-app] #1535 Mul #1534 #187
[mk-app] #1536 the_q!model.impl&%0.d.? #44
[mk-app] #1537 Mul #672 #1536
[mk-app] #1538 = #1535 #1537
[mk-app] #1539 = #1533 #1538
[mk-app] #1540 pattern #1533
[mk-quant] #1541 internal_the_q!model.q_is.?_definition 3 #1540 #1539
[attach-var-names] #1541 (|d!| ; |Poly|) (|n!| ; |Poly|) (|r!| ; |Poly|)
[mk-app] #1542 => #1532 #1541
[mk-app] #1543 not #1532
[mk-app] #1544 or #1543 #1541
[inst-discovered] theory-solving 0 basic# ; #1542
[mk-app] #1545 = #1542 #1544
[instance] 0 #1545
[attach-enode] #1545 0
[end-of-instance]
[mk-app] #1545 fuel_bool_default #811
[mk-app] #1546 fuel_bool #811
[mk-app] #1547 the_q!model.q_le_frac.? #44 #33 #34
[mk-app] #1548 <= #1535 #1537
[mk-app] #1549 = #1547 #1548
[mk-app] #1550 pattern #1547
[mk-quant] #1551 internal_the_q!model.q_le_frac.?_definition 3 #1550 #1549
[attach-var-names] #1551 (|d!| ; |Poly|) (|n!| ; |Poly|) (|r!| ; |Poly|)
[mk-app] #1552 => #1546 #1551
[attach-meaning] #366 arith (- 1)
[mk-app] #1553 * #366 #1537
[mk-app] #1554 + #1535 #1553
[mk-app] #1555 <= #1554 #337
[inst-discovered] theory-solving 0 arith# ; #1548
[mk-app] #1556 = #1548 #1555
[instance] 0 #1556
[attach-enode] #1556 0
[end-of-instance]
[mk-app] #1556 = #1547 #1555
[mk-quant] #1557 internal_the_q!model.q_le_frac.?_definition 3 #1550 #1556
[attach-var-names] #1557 (|d!| ; |Poly|) (|n!| ; |Poly|) (|r!| ; |Poly|)
[mk-app] #1558 not #1546
[mk-app] #1559 or #1558 #1557
[mk-app] #1560 => #1546 #1557
[inst-discovered] theory-solving 0 basic# ; #1560
[mk-app] #1561 = #1560 #1559
[instance] 0 #1561
[attach-enode] #1561 0
[end-of-instance]
[mk-app] #1560 fuel_bool_default #812
[mk-app] #1561 fuel_bool #812
[mk-app] #1562 the_q!model.q_ge_frac.? #44 #33 #34
[mk-app] #1563 >= #1535 #1537
[mk-app] #1564 = #1562 #1563
[mk-app] #1565 pattern #1562
[mk-quant] #1566 internal_the_q!model.q_ge_frac.?_definition 3 #1565 #1564
[attach-var-names] #1566 (|d!| ; |Poly|) (|n!| ; |Poly|) (|r!| ; |Poly|)
[mk-app] #1567 => #1561 #1566
[attach-meaning] #366 arith (- 1)
[mk-app] #1568 >= #1554 #337
[inst-discovered] theory-solving 0 arith# ; #1563
[mk-app] #1569 = #1563 #1568
[instance] 0 #1569
[attach-enode] #1569 0
[end-of-instance]
[mk-app] #1569 = #1562 #1568
[mk-quant] #1570 internal_the_q!model.q_ge_frac.?_definition 3 #1565 #1569
[attach-var-names] #1570 (|d!| ; |Poly|) (|n!| ; |Poly|) (|r!| ; |Poly|)
[mk-app] #1571 not #1561
[mk-app] #1572 or #1571 #1570
[mk-app] #1573 => #1561 #1570
[inst-discovered] theory-solving 0 basic# ; #1573
[mk-app] #1574 = #1573 #1572
[instance] 0 #1574
[attach-enode] #1574 0
[end-of-instance]
[mk-app] #1573 fuel_bool_default #813
[mk-app] #1574 fuel_bool #813
[mk-app] #1575 the_q!model.precision_b.? #34
[mk-app] #1576 Int
[attach-meaning] #1576 arith 61
[mk-app] #1577 = #1575 #1576
[mk-app] #1578 pattern #1575
[mk-quant] #1579 internal_the_q!model.precision_b.?_definition 1 #1578 #1577
[attach-var-names] #1579 (|no%param| ; |Poly|)
[mk-app] #1580 => #1574 #1579
[mk-app] #1581 not #1574
[mk-app] #1582 or #1581 #1579
[inst-discovered] theory-solving 0 basic# ; #1580
[mk-app] #1583 = #1580 #1582
[instance] 0 #1583
[attach-enode] #1583 0
[end-of-instance]
[mk-app] #1583 <= #337 #1575
[mk-app] #1584 => #186 #1583
[mk-quant] #1585 internal_the_q!model.precision_b.?_pre_post_definition 1 #1578 #1584
[attach-var-names] #1585 (|no%param| ; |Poly|)
[attach-meaning] #366 arith (- 1)
[mk-app] #1586 * #366 #1575
[mk-app] #1587 >= #1575 #337
[inst-discovered] theory-solving 0 arith# ; #1583
[mk-app] #1586 = #1583 #1587
[instance] 0 #1586
[attach-enode] #1586 0
[end-of-instance]
[mk-app] #1586 or #193 #1587
[mk-app] #1588 => #186 #1587
[inst-discovered] theory-solving 0 basic# ; #1588
[mk-app] #1589 = #1588 #1586
[instance] 0 #1589
[attach-enode] #1589 0
[end-of-instance]
[mk-quant] #1588 internal_the_q!model.precision_b.?_pre_post_definition 1 #1578 #1586
[attach-var-names] #1588 (|no%param| ; |Poly|)
[mk-app] #1589 fuel_bool_default #814
[mk-app] #1590 fuel_bool #814
[mk-app] #1591 the_q!model.within_error_bound.? #44 #33 #34
[mk-app] #1592 Sub #1535 #1537
[mk-app] #1593 I #1592
[mk-app] #1594 the_q!model.abs_int.? #1593
[mk-app] #1595 the_q!model.precision_b.? #1399
[mk-app] #1596 I #1595
[mk-app] #1597 the_q!model.pow2.? #1596
[mk-app] #1598 Mul #1594 #1597
[mk-app] #1599 I #1318
[mk-app] #1600 the_q!model.max_int.? #34 #1599
[mk-app] #1601 Mul #1536 #1600
[mk-app] #1602 <= #1598 #1601
[mk-app] #1603 = #1591 #1602
[mk-app] #1604 pattern #1591
[mk-quant] #1605 internal_the_q!model.within_error_bound.?_definition 3 #1604 #1603
[attach-var-names] #1605 (|d!| ; |Poly|) (|n!| ; |Poly|) (|r!| ; |Poly|)
[mk-app] #1606 => #1590 #1605
[attach-meaning] #366 arith (- 1)
[mk-app] #1607 * #366 #1601
[mk-app] #1608 + #1598 #1607
[mk-app] #1609 <= #1608 #337
[inst-discovered] theory-solving 0 arith# ; #1602
[mk-app] #1610 = #1602 #1609
[instance] 0 #1610
[attach-enode] #1610 0
[end-of-instance]
[mk-app] #1610 = #1591 #1609
[mk-quant] #1611 internal_the_q!model.within_error_bound.?_definition 3 #1604 #1610
[attach-var-names] #1611 (|d!| ; |Poly|) (|n!| ; |Poly|) (|r!| ; |Poly|)
[mk-app] #1612 not #1590
[mk-app] #1613 or #1612 #1611
[mk-app] #1614 => #1590 #1611
[inst-discovered] theory-solving 0 basic# ; #1614
[mk-app] #1615 = #1614 #1613
[instance] 0 #1615
[attach-enode] #1615 0
[end-of-instance]
[mk-app] #1614 fuel_bool_default #815
[mk-app] #1615 fuel_bool #815
[mk-app] #1616 the_q!model.within_error_bound_k.? #64 #44 #33 #34
[mk-app] #1617 the_q!model.impl&%0.n.? #64
[mk-app] #1618 Mul #1617 #672
[mk-app] #1619 the_q!model.impl&%0.d.? #64
[mk-app] #1620 Mul #662 #1619
[mk-app] #1621 Sub #1618 #1620
[mk-app] #1622 I #1621
[mk-app] #1623 the_q!model.abs_int.? #1622
[mk-app] #1624 Mul #1623 #1597
[mk-app] #1625 Mul #187 #1619
[mk-app] #1626 the_q!model.abs_int.? #44
[mk-app] #1627 I #1626
[mk-app] #1628 the_q!model.max_int.? #33 #1627
[mk-app] #1629 Mul #1625 #1628
[mk-app] #1630 <= #1624 #1629
[mk-app] #1631 = #1616 #1630
[mk-app] #1632 pattern #1616
[mk-quant] #1633 internal_the_q!model.within_error_bound_k.?_definition 4 #1632 #1631
[attach-var-names] #1633 (|k!| ; |Poly|) (|d!| ; |Poly|) (|n!| ; |Poly|) (|r!| ; |Poly|)
[mk-app] #1634 => #1615 #1633
[attach-meaning] #366 arith (- 1)
[mk-app] #1635 * #366 #1629
[mk-app] #1636 + #1624 #1635
[mk-app] #1637 <= #1636 #337
[inst-discovered] theory-solving 0 arith# ; #1630
[mk-app] #1638 = #1630 #1637
[instance] 0 #1638
[attach-enode] #1638 0
[end-of-instance]
[mk-app] #1638 = #1616 #1637
[mk-quant] #1639 internal_the_q!model.within_error_bound_k.?_definition 4 #1632 #1638
[attach-var-names] #1639 (|k!| ; |Poly|) (|d!| ; |Poly|) (|n!| ; |Poly|) (|r!| ; |Poly|)
[mk-app] #1640 not #1615
[mk-app] #1641 or #1640 #1639
[mk-app] #1642 => #1615 #1639
[inst-discovered] theory-solving 0 basic# ; #1642
[mk-app] #1643 = #1642 #1641
[instance] 0 #1643
[attach-enode] #1643 0
[end-of-instance]
[mk-app] #1642 fuel_bool_default #816
[mk-app] #1643 fuel_bool #816
[mk-var] #1644 4
[mk-app] #1645 the_q!model.within_abs_error.? #1644 #64 #44 #33 #34
[mk-app] #1646 the_q!model.impl&%0.n.? #1644
[mk-app] #1647 Mul #1646 #662
[mk-app] #1648 %I #64
[mk-app] #1649 the_q!model.impl&%0.d.? #1644
[mk-app] #1650 Mul #1648 #1649
[mk-app] #1651 Sub #1647 #1650
[mk-app] #1652 I #1651
[mk-app] #1653 the_q!model.abs_int.? #1652
[mk-app] #1654 Mul #1653 #1597
[mk-app] #1655 Mul #672 #187
[mk-app] #1656 Mul #1649 #662
[mk-app] #1657 Mul #1655 #1656
[mk-app] #1658 <= #1654 #1657
[mk-app] #1659 = #1645 #1658
[mk-app] #1660 pattern #1645
[mk-quant] #1661 internal_the_q!model.within_abs_error.?_definition 5 #1660 #1659
[attach-var-names] #1661 (|m!| ; |Poly|) (|k!| ; |Poly|) (|d!| ; |Poly|) (|n!| ; |Poly|) (|r!| ; |Poly|)
[mk-app] #1662 => #1643 #1661
[attach-meaning] #366 arith (- 1)
[mk-app] #1663 * #366 #1657
[mk-app] #1664 + #1654 #1663
[mk-app] #1665 <= #1664 #337
[inst-discovered] theory-solving 0 arith# ; #1658
[mk-app] #1666 = #1658 #1665
[instance] 0 #1666
[attach-enode] #1666 0
[end-of-instance]
[mk-app] #1666 = #1645 #1665
[mk-quant] #1667 internal_the_q!model.within_abs_error.?_definition 5 #1660 #1666
[attach-var-names] #1667 (|m!| ; |Poly|) (|k!| ; |Poly|) (|d!| ; |Poly|) (|n!| ; |Poly|) (|r!| ; |Poly|)
[mk-app] #1668 not #1643
[mk-app] #1669 or #1668 #1667
[mk-app] #1670 => #1643 #1667
[inst-discovered] theory-solving 0 basic# ; #1670
[mk-app] #1671 = #1670 #1669
[instance] 0 #1671
[attach-enode] #1671 0
[end-of-instance]
[mk-app] #1670 tr_bound%core!ops.function.FnOnce. #1058 #46 #1023 #264
[mk-app] #1671 => #1057 #1670
[mk-app] #1672 pattern #1670
[mk-quant] #1673 internal_core__ops__function__impls__impl&__2_trait_impl_definition 4 #1672 #1671
[attach-var-names] #1673 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #1674 or #1065 #1670
[inst-discovered] theory-solving 0 basic# ; #1671
[mk-app] #1675 = #1671 #1674
[instance] 0 #1675
[attach-enode] #1675 0
[end-of-instance]
[mk-quant] #1675 internal_core__ops__function__impls__impl&__2_trait_impl_definition 4 #1672 #1674
[attach-var-names] #1675 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #1676 tr_bound%core!ops.function.FnMut. #1058 #46 #1023 #264
[mk-app] #1677 => #1057 #1676
[mk-app] #1678 pattern #1676
[mk-quant] #1679 internal_core__ops__function__impls__impl&__1_trait_impl_definition 4 #1678 #1677
[attach-var-names] #1679 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #1680 or #1065 #1676
[inst-discovered] theory-solving 0 basic# ; #1677
[mk-app] #1681 = #1677 #1680
[instance] 0 #1681
[attach-enode] #1681 0
[end-of-instance]
[mk-quant] #1681 internal_core__ops__function__impls__impl&__1_trait_impl_definition 4 #1678 #1680
[attach-var-names] #1681 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #1682 tr_bound%core!ops.function.Fn. #1058 #46 #1023 #264
[mk-app] #1683 => #1057 #1682
[mk-app] #1684 pattern #1682
[mk-quant] #1685 internal_core__ops__function__impls__impl&__0_trait_impl_definition 4 #1684 #1683
[attach-var-names] #1685 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #1686 or #1065 #1682
[inst-discovered] theory-solving 0 basic# ; #1683
[mk-app] #1687 = #1683 #1686
[instance] 0 #1687
[attach-enode] #1687 0
[end-of-instance]
[mk-quant] #1687 internal_core__ops__function__impls__impl&__0_trait_impl_definition 4 #1684 #1686
[attach-var-names] #1687 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #1688 tr_bound%core!ops.function.FnOnce. #1099 #264 #1093 #1094
[mk-app] #1689 => #1098 #1688
[mk-app] #1690 pattern #1688
[mk-quant] #1691 internal_alloc__boxed__impl&__31_trait_impl_definition 6 #1690 #1689
[attach-var-names] #1691 (|A&| ; |Type|) (|A&.| ; |Dcr|) (|F&| ; |Type|) (|F&.| ; |Dcr|) (|Args&| ; |Type|) (|Args&.| ; |Dcr|)
[mk-app] #1692 or #1106 #1688
[inst-discovered] theory-solving 0 basic# ; #1689
[mk-app] #1693 = #1689 #1692
[instance] 0 #1693
[attach-enode] #1693 0
[end-of-instance]
[mk-quant] #1693 internal_alloc__boxed__impl&__31_trait_impl_definition 6 #1690 #1692
[attach-var-names] #1693 (|A&| ; |Type|) (|A&.| ; |Dcr|) (|F&| ; |Type|) (|F&.| ; |Dcr|) (|Args&| ; |Type|) (|Args&.| ; |Dcr|)
[mk-app] #1694 and #1095 #1025 #1096 #1130 #1051
[mk-app] #1695 tr_bound%core!ops.function.FnMut. #1099 #264 #1093 #1094
[mk-app] #1696 => #1694 #1695
[mk-app] #1697 pattern #1695
[mk-quant] #1698 internal_alloc__boxed__impl&__32_trait_impl_definition 6 #1697 #1696
[attach-var-names] #1698 (|A&| ; |Type|) (|A&.| ; |Dcr|) (|F&| ; |Type|) (|F&.| ; |Dcr|) (|Args&| ; |Type|) (|Args&.| ; |Dcr|)
[mk-app] #1699 not #1694
[mk-app] #1700 or #1699 #1695
[inst-discovered] theory-solving 0 basic# ; #1696
[mk-app] #1701 = #1696 #1700
[instance] 0 #1701
[attach-enode] #1701 0
[end-of-instance]
[mk-quant] #1701 internal_alloc__boxed__impl&__32_trait_impl_definition 6 #1697 #1700
[attach-var-names] #1701 (|A&| ; |Type|) (|A&.| ; |Dcr|) (|F&| ; |Type|) (|F&.| ; |Dcr|) (|Args&| ; |Type|) (|Args&.| ; |Dcr|)
[mk-app] #1702 tr_bound%core!ops.function.Fn. #1023 #264 #1093 #1094
[mk-app] #1703 and #1095 #1025 #1096 #1702 #1051
[mk-app] #1704 tr_bound%core!ops.function.Fn. #1099 #264 #1093 #1094
[mk-app] #1705 => #1703 #1704
[mk-app] #1706 pattern #1704
[mk-quant] #1707 internal_alloc__boxed__impl&__33_trait_impl_definition 6 #1706 #1705
[attach-var-names] #1707 (|A&| ; |Type|) (|A&.| ; |Dcr|) (|F&| ; |Type|) (|F&.| ; |Dcr|) (|Args&| ; |Type|) (|Args&.| ; |Dcr|)
[mk-app] #1708 not #1703
[mk-app] #1709 or #1708 #1704
[inst-discovered] theory-solving 0 basic# ; #1705
[mk-app] #1710 = #1705 #1709
[instance] 0 #1710
[attach-enode] #1710 0
[end-of-instance]
[mk-quant] #1710 internal_alloc__boxed__impl&__33_trait_impl_definition 6 #1706 #1709
[attach-var-names] #1710 (|A&| ; |Type|) (|A&.| ; |Dcr|) (|F&| ; |Type|) (|F&.| ; |Dcr|) (|Args&| ; |Type|) (|Args&.| ; |Dcr|)
[mk-app] #1711 tr_bound%core!ops.function.FnMut. #121 #47 #1023 #264
[mk-app] #1712 => #1077 #1711
[mk-app] #1713 pattern #1711
[mk-quant] #1714 internal_core__ops__function__impls__impl&__3_trait_impl_definition 4 #1713 #1712
[attach-var-names] #1714 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #1715 or #1083 #1711
[inst-discovered] theory-solving 0 basic# ; #1712
[mk-app] #1716 = #1712 #1715
[instance] 0 #1716
[attach-enode] #1716 0
[end-of-instance]
[mk-quant] #1716 internal_core__ops__function__impls__impl&__3_trait_impl_definition 4 #1713 #1715
[attach-var-names] #1716 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #1717 tr_bound%core!alloc.Allocator. #1058 #46
[mk-app] #1718 => #1051 #1717
[mk-app] #1719 pattern #1717
[mk-quant] #1720 internal_core__alloc__impl&__2_trait_impl_definition 2 #1719 #1718
[attach-var-names] #1720 (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #1721 not #1051
[mk-app] #1722 or #1721 #1717
[inst-discovered] theory-solving 0 basic# ; #1718
[mk-app] #1723 = #1718 #1722
[instance] 0 #1723
[attach-enode] #1723 0
[end-of-instance]
[mk-quant] #1723 internal_core__alloc__impl&__2_trait_impl_definition 2 #1719 #1722
[attach-var-names] #1723 (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #1724 tr_bound%core!alloc.Allocator. #121 #47
[mk-app] #1725 => #1051 #1724
[mk-app] #1726 pattern #1724
[mk-quant] #1727 internal_core__alloc__impl&__3_trait_impl_definition 2 #1726 #1725
[attach-var-names] #1727 (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #1728 or #1721 #1724
[inst-discovered] theory-solving 0 basic# ; #1725
[mk-app] #1729 = #1725 #1728
[instance] 0 #1729
[attach-enode] #1729 0
[end-of-instance]
[mk-quant] #1729 internal_core__alloc__impl&__3_trait_impl_definition 2 #1726 #1728
[attach-var-names] #1729 (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #1730 tr_bound%core!alloc.Allocator. #1023 #264
[mk-app] #1731 and #1025 #1730 #1051
[mk-app] #1732 tr_bound%core!alloc.Allocator. #1099 #264
[mk-app] #1733 => #1731 #1732
[mk-app] #1734 pattern #1732
[mk-quant] #1735 internal_alloc__boxed__impl&__49_trait_impl_definition 4 #1734 #1733
[attach-var-names] #1735 (|A&| ; |Type|) (|A&.| ; |Dcr|) (|T&| ; |Type|) (|T&.| ; |Dcr|)
[mk-app] #1736 not #1731
[mk-app] #1737 or #1736 #1732
[inst-discovered] theory-solving 0 basic# ; #1733
[mk-app] #1738 = #1733 #1737
[instance] 0 #1738
[attach-enode] #1738 0
[end-of-instance]
[mk-quant] #1738 internal_alloc__boxed__impl&__49_trait_impl_definition 4 #1734 #1737
[attach-var-names] #1738 (|A&| ; |Type|) (|A&.| ; |Dcr|) (|T&| ; |Type|) (|T&.| ; |Dcr|)
[mk-app] #1739 RC #45 #46 #1023
[mk-app] #1740 tr_bound%core!alloc.Allocator. #1739 #264
[mk-app] #1741 => #1731 #1740
[mk-app] #1742 pattern #1740
[mk-quant] #1743 internal_alloc__rc__impl&__115_trait_impl_definition 4 #1742 #1741
[attach-var-names] #1743 (|A&| ; |Type|) (|A&.| ; |Dcr|) (|T&| ; |Type|) (|T&.| ; |Dcr|)
[mk-app] #1744 or #1736 #1740
[inst-discovered] theory-solving 0 basic# ; #1741
[mk-app] #1745 = #1741 #1744
[instance] 0 #1745
[attach-enode] #1745 0
[end-of-instance]
[mk-quant] #1745 internal_alloc__rc__impl&__115_trait_impl_definition 4 #1742 #1744
[attach-var-names] #1745 (|A&| ; |Type|) (|A&.| ; |Dcr|) (|T&| ; |Type|) (|T&.| ; |Dcr|)
[mk-app] #1746 ARC #45 #46 #1023
[mk-app] #1747 tr_bound%core!alloc.Allocator. #1746 #264
[mk-app] #1748 => #1731 #1747
[mk-app] #1749 pattern #1747
[mk-quant] #1750 internal_alloc__sync__impl&__117_trait_impl_definition 4 #1749 #1748
[attach-var-names] #1750 (|A&| ; |Type|) (|A&.| ; |Dcr|) (|T&| ; |Type|) (|T&.| ; |Dcr|)
[mk-app] #1751 or #1736 #1747
[inst-discovered] theory-solving 0 basic# ; #1748
[mk-app] #1752 = #1748 #1751
[instance] 0 #1752
[attach-enode] #1752 0
[end-of-instance]
[mk-quant] #1752 internal_alloc__sync__impl&__117_trait_impl_definition 4 #1749 #1751
[attach-var-names] #1752 (|A&| ; |Type|) (|A&.| ; |Dcr|) (|T&| ; |Type|) (|T&.| ; |Dcr|)
[mk-app] #1753 ens%the_q!model.lemma_pow2_pos. #123
[mk-app] #1754 the_q!model.pow2.? #166
[mk-app] #1755 > #1754 #337
[mk-app] #1756 = #1753 #1755
[mk-app] #1757 pattern #1753
[mk-quant] #1758 internal_ens__the_q!model.lemma_pow2_pos._definition 1 #1757 #1756
[attach-var-names] #1758 (|n!| ; |Int|)
[mk-app] #1759 <= #1754 #337
[mk-app] #1760 not #1759
[inst-discovered] theory-solving 0 arith# ; #1755
[mk-app] #1761 = #1755 #1760
[instance] 0 #1761
[attach-enode] #1761 0
[end-of-instance]
[mk-app] #1761 = #1759 #1753
[mk-app] #1762 not #1761
[mk-app] #1763 = #1753 #1760
[inst-discovered] theory-solving 0 basic# ; #1763
[mk-app] #1764 = #1763 #1762
[instance] 0 #1764
[attach-enode] #1764 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1762
[mk-app] #1763 = #1762 #1762
[instance] 0 #1763
[attach-enode] #1763 0
[end-of-instance]
[mk-quant] #1763 internal_ens__the_q!model.lemma_pow2_pos._definition 1 #1757 #1762
[attach-var-names] #1763 (|n!| ; |Int|)
[mk-app] #1760 req%the_q!model.lemma_pow2_mono. #220 #123
[mk-app] #1764 %%global_location_label%%0
[mk-app] #1765 <= #220 #123
[mk-app] #1766 => #1764 #1765
[mk-app] #1767 = #1760 #1766
[mk-app] #1768 pattern #1760
[mk-quant] #1769 internal_req__the_q!model.lemma_pow2_mono._definition 2 #1768 #1767
[attach-var-names] #1769 (|b!| ; |Int|) (|a!| ; |Int|)
[attach-meaning] #366 arith (- 1)
[mk-app] #1770 * #366 #123
[mk-app] #1771 + #1770 #220
[attach-meaning] #366 arith (- 1)
[mk-app] #1770 >= #778 #337
[inst-discovered] theory-solving 0 arith# ; #1765
[mk-app] #1771 = #1765 #1770
[instance] 0 #1771
[attach-enode] #1771 0
[end-of-instance]
[mk-app] #1771 not #1764
[mk-app] #1772 or #1771 #1770
[mk-app] #1773 => #1764 #1770
[inst-discovered] theory-solving 0 basic# ; #1773
[mk-app] #1774 = #1773 #1772
[instance] 0 #1774
[attach-enode] #1774 0
[end-of-instance]
[mk-app] #1773 = #1760 #1772
[mk-quant] #1774 internal_req__the_q!model.lemma_pow2_mono._definition 2 #1768 #1773
[attach-var-names] #1774 (|b!| ; |Int|) (|a!| ; |Int|)
[mk-app] #1775 ens%the_q!model.lemma_pow2_mono. #220 #123
[mk-app] #1776 the_q!model.pow2.? #767
[mk-app] #1777 <= #1776 #1754
[mk-app] #1778 = #1775 #1777
[mk-app] #1779 pattern #1775
[mk-quant] #1780 internal_ens__the_q!model.lemma_pow2_mono._definition 2 #1779 #1778
[attach-var-names] #1780 (|b!| ; |Int|) (|a!| ; |Int|)
[attach-meaning] #366 arith (- 1)
[mk-app] #1781 * #366 #1754
[mk-app] #1782 + #1781 #1776
[attach-meaning] #366 arith (- 1)
[mk-app] #1783 * #366 #1776
[mk-app] #1784 + #1754 #1783
[mk-app] #1781 >= #1784 #337
[inst-discovered] theory-solving 0 arith# ; #1777
[mk-app] #1782 = #1777 #1781
[instance] 0 #1782
[attach-enode] #1782 0
[end-of-instance]
[mk-app] #1782 = #1775 #1781
[mk-quant] #1785 internal_ens__the_q!model.lemma_pow2_mono._definition 2 #1779 #1782
[attach-var-names] #1785 (|b!| ; |Int|) (|a!| ; |Int|)
[mk-app] #1786 ens%the_q!model.lemma_pow2_add. #220 #123
[mk-app] #1787 nClip #543
[mk-app] #1788 I #1787
[mk-app] #1789 the_q!model.pow2.? #1788
[mk-app] #1790 Mul #1776 #1754
[mk-app] #1791 = #1789 #1790
[mk-app] #1792 = #1786 #1791
[mk-app] #1793 pattern #1786
[mk-quant] #1794 internal_ens__the_q!model.lemma_pow2_add._definition 2 #1793 #1792
[attach-var-names] #1794 (|b!| ; |Int|) (|a!| ; |Int|)
[attach-enode] #292 0
[mk-app] #1795 Real
[attach-meaning] #1795 arith 1
[attach-enode] #1795 0
[attach-enode] #337 0
[attach-enode] #598 0
[inst-discovered] theory-solving 0 basic# ; #914
[mk-app] #1796 = #914 #914
[instance] 0 #1796
[attach-enode] #1796 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #919
[mk-app] #1796 = #919 #919
[instance] 0 #1796
[attach-enode] #1796 0
[end-of-instance]
[mk-app] #1796 not #1
[inst-discovered] theory-solving 0 basic# ; #1796
[mk-app] #1797 = #1796 #2
[instance] 0 #1797
[attach-enode] #1797 0
[end-of-instance]
[mk-app] #1796 or #2 #943
[inst-discovered] theory-solving 0 basic# ; #1796
[mk-app] #1797 = #1796 #943
[instance] 0 #1797
[attach-enode] #1797 0
[end-of-instance]
[mk-app] #945 not #1527
[inst-discovered] theory-solving 0 basic# ; #1530
[mk-app] #945 = #1530 #1530
[instance] 0 #945
[attach-enode] #945 0
[end-of-instance]
[mk-app] #945 not #1759
[inst-discovered] theory-solving 0 basic# ; #1762
[mk-app] #945 = #1762 #1762
[instance] 0 #945
[attach-enode] #945 0
[end-of-instance]
[mk-app] #945 not #1759
[inst-discovered] theory-solving 0 basic# ; #1762
[mk-app] #945 = #1762 #1762
[instance] 0 #945
[attach-enode] #945 0
[end-of-instance]
[mk-app] #945 not #1527
[inst-discovered] theory-solving 0 basic# ; #1530
[mk-app] #945 = #1530 #1530
[instance] 0 #945
[attach-enode] #945 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #919
[mk-app] #945 = #919 #919
[instance] 0 #945
[attach-enode] #945 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #914
[mk-app] #945 = #914 #914
[instance] 0 #945
[attach-enode] #945 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #914
[mk-app] #945 = #914 #914
[instance] 0 #945
[attach-enode] #945 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #919
[mk-app] #945 = #919 #919
[instance] 0 #945
[attach-enode] #945 0
[end-of-instance]
[mk-app] #945 not #1527
[inst-discovered] theory-solving 0 basic# ; #1530
[mk-app] #945 = #1530 #1530
[instance] 0 #945
[attach-enode] #945 0
[end-of-instance]
[mk-app] #945 not #1759
[inst-discovered] theory-solving 0 basic# ; #1762
[mk-app] #945 = #1762 #1762
[instance] 0 #945
[attach-enode] #945 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #914
[mk-app] #945 = #914 #914
[instance] 0 #945
[attach-enode] #945 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #919
[mk-app] #945 = #919 #919
[instance] 0 #945
[attach-enode] #945 0
[end-of-instance]
[mk-app] #945 not #1256
[mk-app] #946 k$!skolem_user_the_q__model__divides_2!0 #34 #33
[mk-app] #1796 Mul #672 #946
[mk-app] #1797 = #187 #1796
[mk-app] #1798 not #1258
[mk-quant] #1799 user_the_q__model__divides_2 1 #1259 #1798
[attach-var-names] #1799 (|k$| ; |Int|)
[mk-app] #1800 or #1256 #1799
[mk-app] #1801 or #945 #1797
[mk-app] #1802 and #1801 #1800
[mk-quant] #1803 internal_the_q!model.divides.?_definition 2 #1262 #1802
[attach-var-names] #1803 (|n!| ; |Poly|) (|d!| ; |Poly|)
[mk-app] #1804 or #1265 #1803
[mk-app] #1805 not #1527
[inst-discovered] theory-solving 0 basic# ; #1530
[mk-app] #1805 = #1530 #1530
[instance] 0 #1805
[attach-enode] #1805 0
[end-of-instance]
[mk-app] #1805 not #1759
[inst-discovered] theory-solving 0 basic# ; #1762
[mk-app] #1805 = #1762 #1762
[instance] 0 #1805
[attach-enode] #1805 0
[end-of-instance]
[mk-app] #1266 not #68
[mk-app] #1805 not #69
[mk-app] #1806 or #1266 #1805
[mk-app] #1807 not #1806
[inst-discovered] theory-solving 0 basic# ; #70
[mk-app] #1808 = #70 #1807
[instance] 0 #1808
[attach-enode] #1808 0
[end-of-instance]
[mk-app] #1808 not #1807
[inst-discovered] theory-solving 0 basic# ; #1808
[mk-app] #1809 = #1808 #1806
[instance] 0 #1809
[attach-enode] #1809 0
[end-of-instance]
[mk-app] #1808 or #1266 #1805 #72
[mk-app] #1809 or #1806 #72
[inst-discovered] theory-solving 0 basic# ; #1809
[mk-app] #1810 = #1809 #1808
[instance] 0 #1810
[attach-enode] #1810 0
[end-of-instance]
[mk-quant] #1809 prelude_mut_ref_update_has_type 4 #74 #1808
[attach-var-names] #1809 (|arg| ; |Poly|) (|t| ; |Type|) (|d| ; |Dcr|) (|m| ; |Poly|)
[mk-app] #1806 not #146
[mk-app] #1807 not #154
[mk-app] #1810 or #1806 #1807
[mk-app] #1811 not #1810
[inst-discovered] theory-solving 0 basic# ; #155
[mk-app] #1812 = #155 #1811
[instance] 0 #1812
[attach-enode] #1812 0
[end-of-instance]
[mk-quant] #1812 prelude_as_type 2 #151 #1811
[attach-var-names] #1812 (|t| ; |Type|) (|x| ; |Poly|)
[mk-app] #1813 not #348
[mk-app] #1814 not #347
[mk-app] #1815 or #1813 #1814
[mk-app] #1816 not #1815
[inst-discovered] theory-solving 0 basic# ; #350
[mk-app] #1817 = #350 #1816
[instance] 0 #1817
[attach-enode] #1817 0
[end-of-instance]
[mk-quant] #1817 prelude_nat_clip 1 #344 #1816
[attach-var-names] #1817 (|i| ; |Int|)
[mk-app] #1818 or #346 #373
[mk-app] #1819 not #1818
[inst-discovered] theory-solving 0 basic# ; #376
[mk-app] #1820 = #376 #1819
[instance] 0 #1820
[attach-enode] #1820 0
[end-of-instance]
[mk-app] #1820 not #1819
[inst-discovered] theory-solving 0 basic# ; #1820
[mk-app] #1821 = #1820 #1818
[instance] 0 #1821
[attach-enode] #1821 0
[end-of-instance]
[mk-app] #1820 or #346 #373 #358
[mk-app] #1821 or #1818 #358
[inst-discovered] theory-solving 0 basic# ; #1821
[mk-app] #1822 = #1821 #1820
[instance] 0 #1822
[attach-enode] #1822 0
[end-of-instance]
[mk-app] #1821 not #365
[mk-app] #1822 not #1820
[mk-app] #1823 or #1821 #367 #1822
[mk-app] #1824 not #1823
[mk-app] #1825 and #365 #368 #1820
[inst-discovered] theory-solving 0 basic# ; #1825
[mk-app] #1826 = #1825 #1824
[instance] 0 #1826
[attach-enode] #1826 0
[end-of-instance]
[mk-quant] #1825 prelude_u_clip 2 #361 #1824
[attach-var-names] #1825 (|i| ; |Int|) (|bits| ; |Int|)
[mk-app] #1818 not #399
[mk-app] #1819 or #1818 #404
[mk-app] #1826 not #1819
[inst-discovered] theory-solving 0 basic# ; #407
[mk-app] #1827 = #407 #1826
[instance] 0 #1827
[attach-enode] #1827 0
[end-of-instance]
[mk-app] #1827 not #1826
[inst-discovered] theory-solving 0 basic# ; #1827
[mk-app] #1828 = #1827 #1819
[instance] 0 #1828
[attach-enode] #1828 0
[end-of-instance]
[mk-app] #1827 or #1818 #404 #385
[mk-app] #1828 or #1819 #385
[inst-discovered] theory-solving 0 basic# ; #1828
[mk-app] #1829 = #1828 #1827
[instance] 0 #1829
[attach-enode] #1829 0
[end-of-instance]
[mk-app] #1828 not #392
[mk-app] #1829 not #1827
[mk-app] #1830 or #1828 #395 #1829
[mk-app] #1831 not #1830
[mk-app] #1832 and #392 #398 #1827
[inst-discovered] theory-solving 0 basic# ; #1832
[mk-app] #1833 = #1832 #1831
[instance] 0 #1833
[attach-enode] #1833 0
[end-of-instance]
[mk-quant] #1832 prelude_i_clip 2 #388 #1831
[attach-var-names] #1832 (|i| ; |Int|) (|bits| ; |Int|)
[mk-app] #1819 not #431
[mk-app] #1826 not #394
[mk-app] #1833 or #1819 #1826
[mk-app] #1834 not #1833
[inst-discovered] theory-solving 0 basic# ; #430
[mk-app] #1835 = #430 #1834
[instance] 0 #1835
[attach-enode] #1835 0
[end-of-instance]
[mk-app] #1835 not #434
[mk-app] #1836 not #416
[mk-app] #1837 or #1835 #1836
[mk-app] #1838 not #1837
[inst-discovered] theory-solving 0 basic# ; #432
[mk-app] #1839 = #432 #1838
[instance] 0 #1839
[attach-enode] #1839 0
[end-of-instance]
[mk-app] #1839 or #1834 #1838
[mk-app] #1840 not #419
[mk-app] #1841 or #346 #1840
[mk-app] #1842 not #1841
[inst-discovered] theory-solving 0 basic# ; #435
[mk-app] #1843 = #435 #1842
[instance] 0 #1843
[attach-enode] #1843 0
[end-of-instance]
[mk-app] #1843 not #438
[mk-app] #1844 not #422
[mk-app] #1845 or #1843 #1844
[mk-app] #1846 not #1845
[inst-discovered] theory-solving 0 basic# ; #436
[mk-app] #1847 = #436 #1846
[instance] 0 #1847
[attach-enode] #1847 0
[end-of-instance]
[mk-app] #1847 or #1842 #1846
[mk-app] #1848 not #1847
[mk-app] #1849 or #1848 #425
[mk-app] #1850 not #1839
[mk-app] #1851 not #1849
[mk-app] #1852 or #1850 #1851
[mk-app] #1853 not #1852
[mk-app] #1854 and #1839 #1849
[inst-discovered] theory-solving 0 basic# ; #1854
[mk-app] #1855 = #1854 #1853
[instance] 0 #1855
[attach-enode] #1855 0
[end-of-instance]
[mk-quant] #1854 prelude_char_clip 1 #428 #1853
[attach-var-names] #1854 (|i| ; |Int|)
[mk-app] #1855 or #346 #373
[mk-app] #1856 not #1855
[inst-discovered] theory-solving 0 basic# ; #376
[mk-app] #1857 = #376 #1856
[instance] 0 #1857
[attach-enode] #1857 0
[end-of-instance]
[mk-app] #1857 = #1855 #443
[mk-app] #1858 not #1857
[mk-app] #1859 = #443 #1856
[inst-discovered] theory-solving 0 basic# ; #1859
[mk-app] #1860 = #1859 #1858
[instance] 0 #1860
[attach-enode] #1860 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1858
[mk-app] #1859 = #1858 #1858
[instance] 0 #1859
[attach-enode] #1859 0
[end-of-instance]
[mk-quant] #1859 prelude_u_inv 2 #445 #1858
[attach-var-names] #1859 (|i| ; |Int|) (|bits| ; |Int|)
[mk-app] #1856 or #1818 #404
[mk-app] #1860 not #1856
[inst-discovered] theory-solving 0 basic# ; #407
[mk-app] #1861 = #407 #1860
[instance] 0 #1861
[attach-enode] #1861 0
[end-of-instance]
[mk-app] #1861 = #1856 #447
[mk-app] #1862 not #1861
[mk-app] #1863 = #447 #1860
[inst-discovered] theory-solving 0 basic# ; #1863
[mk-app] #1864 = #1863 #1862
[instance] 0 #1864
[attach-enode] #1864 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1862
[mk-app] #1863 = #1862 #1862
[instance] 0 #1863
[attach-enode] #1863 0
[end-of-instance]
[mk-quant] #1863 prelude_i_inv 2 #451 #1862
[attach-var-names] #1863 (|i| ; |Int|) (|bits| ; |Int|)
[inst-discovered] theory-solving 0 basic# ; #435
[mk-app] #1860 = #435 #1842
[instance] 0 #1860
[attach-enode] #1860 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #436
[mk-app] #1860 = #436 #1846
[instance] 0 #1860
[attach-enode] #1860 0
[end-of-instance]
[mk-app] #1860 = #453 #1847
[mk-quant] #1864 prelude_char_inv 1 #457 #1860
[attach-var-names] #1864 (|i| ; |Int|)
[mk-app] #1865 not #633
[mk-app] #1866 or #1865 #346
[mk-app] #1867 not #1866
[inst-discovered] theory-solving 0 basic# ; #634
[mk-app] #1868 = #634 #1867
[instance] 0 #1868
[attach-enode] #1868 0
[end-of-instance]
[mk-app] #1868 not #1867
[inst-discovered] theory-solving 0 basic# ; #1868
[mk-app] #1869 = #1868 #1866
[instance] 0 #1869
[attach-enode] #1869 0
[end-of-instance]
[mk-app] #1867 or #1865 #346 #636
[mk-app] #1868 or #1866 #636
[inst-discovered] theory-solving 0 basic# ; #1868
[mk-app] #1869 = #1868 #1867
[instance] 0 #1869
[attach-enode] #1869 0
[end-of-instance]
[mk-quant] #1866 prelude_mul_nats 2 #564 #1867
[attach-var-names] #1866 (|y| ; |Int|) (|x| ; |Int|)
[mk-app] #1868 or #1865 #646
[mk-app] #1869 not #1868
[inst-discovered] theory-solving 0 basic# ; #648
[mk-app] #1870 = #648 #1869
[instance] 0 #1870
[attach-enode] #1870 0
[end-of-instance]
[mk-app] #1870 not #1869
[inst-discovered] theory-solving 0 basic# ; #1870
[mk-app] #1871 = #1870 #1868
[instance] 0 #1871
[attach-enode] #1871 0
[end-of-instance]
[mk-app] #1869 not #650
[mk-app] #1870 not #649
[mk-app] #1871 or #1869 #1870
[mk-app] #1872 not #1871
[inst-discovered] theory-solving 0 basic# ; #653
[mk-app] #1873 = #653 #1872
[instance] 0 #1873
[attach-enode] #1873 0
[end-of-instance]
[mk-app] #1873 or #1865 #646 #1872
[mk-app] #1874 or #1868 #1872
[inst-discovered] theory-solving 0 basic# ; #1874
[mk-app] #1875 = #1874 #1873
[instance] 0 #1875
[attach-enode] #1875 0
[end-of-instance]
[mk-quant] #1874 prelude_div_unsigned_in_bounds 2 #574 #1873
[attach-var-names] #1874 (|y| ; |Int|) (|x| ; |Int|)
[mk-app] #1868 or #1865 #646
[mk-app] #1875 not #1868
[inst-discovered] theory-solving 0 basic# ; #648
[mk-app] #1876 = #648 #1875
[instance] 0 #1876
[attach-enode] #1876 0
[end-of-instance]
[mk-app] #1876 not #1875
[inst-discovered] theory-solving 0 basic# ; #1876
[mk-app] #1877 = #1876 #1868
[instance] 0 #1877
[attach-enode] #1877 0
[end-of-instance]
[mk-app] #1875 not #663
[mk-app] #1876 or #1875 #667
[mk-app] #1877 not #1876
[inst-discovered] theory-solving 0 basic# ; #669
[mk-app] #1878 = #669 #1877
[instance] 0 #1878
[attach-enode] #1878 0
[end-of-instance]
[mk-app] #1878 or #1865 #646 #1877
[mk-app] #1879 or #1868 #1877
[inst-discovered] theory-solving 0 basic# ; #1879
[mk-app] #1880 = #1879 #1878
[instance] 0 #1880
[attach-enode] #1880 0
[end-of-instance]
[mk-quant] #1879 prelude_mod_unsigned_in_bounds 2 #583 #1878
[attach-var-names] #1879 (|y| ; |Int|) (|x| ; |Int|)
[mk-app] #1868 not #664
[mk-app] #1880 not #673
[mk-app] #1881 or #1868 #1880
[mk-app] #1882 not #1881
[inst-discovered] theory-solving 0 basic# ; #674
[mk-app] #1883 = #674 #1882
[instance] 0 #1883
[attach-enode] #1883 0
[end-of-instance]
[mk-app] #1883 not #1882
[inst-discovered] theory-solving 0 basic# ; #1883
[mk-app] #1884 = #1883 #1881
[instance] 0 #1884
[attach-enode] #1884 0
[end-of-instance]
[mk-app] #1883 or #1868 #1880 #676
[mk-app] #1884 or #1881 #676
[inst-discovered] theory-solving 0 basic# ; #1884
[mk-app] #1885 = #1884 #1883
[instance] 0 #1885
[attach-enode] #1885 0
[end-of-instance]
[mk-quant] #1884 prelude_bit_xor_u_inv 3 #679 #1883
[attach-var-names] #1884 (|bits| ; |Int|) (|y| ; |Poly|) (|x| ; |Poly|)
[mk-app] #1881 not #684
[mk-app] #1882 not #685
[mk-app] #1885 or #1881 #1882
[mk-app] #1886 not #1885
[inst-discovered] theory-solving 0 basic# ; #686
[mk-app] #1887 = #686 #1886
[instance] 0 #1887
[attach-enode] #1887 0
[end-of-instance]
[mk-app] #1887 not #1886
[inst-discovered] theory-solving 0 basic# ; #1887
[mk-app] #1888 = #1887 #1885
[instance] 0 #1888
[attach-enode] #1888 0
[end-of-instance]
[mk-app] #1887 or #1881 #1882 #687
[mk-app] #1888 or #1885 #687
[inst-discovered] theory-solving 0 basic# ; #1888
[mk-app] #1889 = #1888 #1887
[instance] 0 #1889
[attach-enode] #1889 0
[end-of-instance]
[mk-quant] #1888 prelude_bit_xor_i_inv 3 #690 #1887
[attach-var-names] #1888 (|bits| ; |Int|) (|y| ; |Poly|) (|x| ; |Poly|)
[mk-app] #1885 or #1868 #1880
[mk-app] #1886 not #1885
[inst-discovered] theory-solving 0 basic# ; #674
[mk-app] #1889 = #674 #1886
[instance] 0 #1889
[attach-enode] #1889 0
[end-of-instance]
[mk-app] #1889 not #1886
[inst-discovered] theory-solving 0 basic# ; #1889
[mk-app] #1890 = #1889 #1885
[instance] 0 #1890
[attach-enode] #1890 0
[end-of-instance]
[mk-app] #1889 or #1868 #1880 #696
[mk-app] #1890 or #1885 #696
[inst-discovered] theory-solving 0 basic# ; #1890
[mk-app] #1891 = #1890 #1889
[instance] 0 #1891
[attach-enode] #1891 0
[end-of-instance]
[mk-quant] #1890 prelude_bit_or_u_inv 3 #699 #1889
[attach-var-names] #1890 (|bits| ; |Int|) (|y| ; |Poly|) (|x| ; |Poly|)
[mk-app] #1885 or #1881 #1882
[mk-app] #1886 not #1885
[inst-discovered] theory-solving 0 basic# ; #686
[mk-app] #1891 = #686 #1886
[instance] 0 #1891
[attach-enode] #1891 0
[end-of-instance]
[mk-app] #1891 not #1886
[inst-discovered] theory-solving 0 basic# ; #1891
[mk-app] #1892 = #1891 #1885
[instance] 0 #1892
[attach-enode] #1892 0
[end-of-instance]
[mk-app] #1891 or #1881 #1882 #703
[mk-app] #1892 or #1885 #703
[inst-discovered] theory-solving 0 basic# ; #1892
[mk-app] #1893 = #1892 #1891
[instance] 0 #1893
[attach-enode] #1893 0
[end-of-instance]
[mk-quant] #1892 prelude_bit_or_i_inv 3 #706 #1891
[attach-var-names] #1892 (|bits| ; |Int|) (|y| ; |Poly|) (|x| ; |Poly|)
[mk-app] #1885 or #1868 #1880
[mk-app] #1886 not #1885
[inst-discovered] theory-solving 0 basic# ; #674
[mk-app] #1893 = #674 #1886
[instance] 0 #1893
[attach-enode] #1893 0
[end-of-instance]
[mk-app] #1893 not #1886
[inst-discovered] theory-solving 0 basic# ; #1893
[mk-app] #1894 = #1893 #1885
[instance] 0 #1894
[attach-enode] #1894 0
[end-of-instance]
[mk-app] #1893 or #1868 #1880 #711
[mk-app] #1894 or #1885 #711
[inst-discovered] theory-solving 0 basic# ; #1894
[mk-app] #1895 = #1894 #1893
[instance] 0 #1895
[attach-enode] #1895 0
[end-of-instance]
[mk-quant] #1894 prelude_bit_and_u_inv 3 #714 #1893
[attach-var-names] #1894 (|bits| ; |Int|) (|y| ; |Poly|) (|x| ; |Poly|)
[mk-app] #1885 or #1881 #1882
[mk-app] #1886 not #1885
[inst-discovered] theory-solving 0 basic# ; #686
[mk-app] #1895 = #686 #1886
[instance] 0 #1895
[attach-enode] #1895 0
[end-of-instance]
[mk-app] #1895 not #1886
[inst-discovered] theory-solving 0 basic# ; #1895
[mk-app] #1896 = #1895 #1885
[instance] 0 #1896
[attach-enode] #1896 0
[end-of-instance]
[mk-app] #1895 or #1881 #1882 #718
[mk-app] #1896 or #1885 #718
[inst-discovered] theory-solving 0 basic# ; #1896
[mk-app] #1897 = #1896 #1895
[instance] 0 #1897
[attach-enode] #1897 0
[end-of-instance]
[mk-quant] #1896 prelude_bit_and_i_inv 3 #721 #1895
[attach-var-names] #1896 (|bits| ; |Int|) (|y| ; |Poly|) (|x| ; |Poly|)
[mk-app] #1885 not #734
[mk-app] #1886 or #1868 #1885
[mk-app] #1897 not #1886
[inst-discovered] theory-solving 0 basic# ; #733
[mk-app] #1898 = #733 #1897
[instance] 0 #1898
[attach-enode] #1898 0
[end-of-instance]
[mk-app] #1898 not #1897
[inst-discovered] theory-solving 0 basic# ; #1898
[mk-app] #1899 = #1898 #1886
[instance] 0 #1899
[attach-enode] #1899 0
[end-of-instance]
[mk-app] #1897 or #1868 #1885 #728
[mk-app] #1898 or #1886 #728
[inst-discovered] theory-solving 0 basic# ; #1898
[mk-app] #1899 = #1898 #1897
[instance] 0 #1899
[attach-enode] #1899 0
[end-of-instance]
[mk-quant] #1886 prelude_bit_shr_u_inv 3 #731 #1897
[attach-var-names] #1886 (|bits| ; |Int|) (|y| ; |Poly|) (|x| ; |Poly|)
[mk-app] #1898 or #1881 #1885
[mk-app] #1899 not #1898
[inst-discovered] theory-solving 0 basic# ; #744
[mk-app] #1900 = #744 #1899
[instance] 0 #1900
[attach-enode] #1900 0
[end-of-instance]
[mk-app] #1900 not #1899
[inst-discovered] theory-solving 0 basic# ; #1900
[mk-app] #1901 = #1900 #1898
[instance] 0 #1901
[attach-enode] #1901 0
[end-of-instance]
[mk-app] #1899 or #1881 #1885 #739
[mk-app] #1900 or #1898 #739
[inst-discovered] theory-solving 0 basic# ; #1900
[mk-app] #1901 = #1900 #1899
[instance] 0 #1901
[attach-enode] #1901 0
[end-of-instance]
[mk-quant] #1898 prelude_bit_shr_i_inv 3 #742 #1899
[attach-var-names] #1898 (|bits| ; |Int|) (|y| ; |Poly|) (|x| ; |Poly|)
[mk-app] #1900 not #761
[mk-app] #1901 not #129
[mk-app] #1902 or #1900 #1901
[mk-app] #1903 not #1902
[inst-discovered] theory-solving 0 basic# ; #762
[mk-app] #1904 = #762 #1903
[instance] 0 #1904
[attach-enode] #1904 0
[end-of-instance]
[mk-app] #1904 or #760 #1903
[inst-discovered] theory-solving 0 basic# ; #1904
[mk-app] #1905 = #1904 #1904
[instance] 0 #1905
[attach-enode] #1905 0
[end-of-instance]
[mk-app] #1905 = #757 #1904
[mk-quant] #1906 prelude_check_decrease_height 3 #765 #1905
[attach-var-names] #1906 (|otherwise| ; |Bool|) (|prev| ; |Poly|) (|cur| ; |Poly|)
[mk-app] #1907 or #1865 #779
[mk-app] #1908 not #1907
[inst-discovered] theory-solving 0 basic# ; #781
[mk-app] #1909 = #781 #1908
[instance] 0 #1909
[attach-enode] #1909 0
[end-of-instance]
[mk-app] #1909 = #1907 #770
[mk-app] #1910 not #1909
[mk-app] #1911 = #770 #1908
[inst-discovered] theory-solving 0 basic# ; #1911
[mk-app] #1912 = #1911 #1910
[instance] 0 #1912
[attach-enode] #1912 0
[end-of-instance]
[mk-app] #1908 not #1907
[inst-discovered] theory-solving 0 basic# ; #1910
[mk-app] #1908 = #1910 #1910
[instance] 0 #1908
[attach-enode] #1908 0
[end-of-instance]
[mk-quant] #1908 prelude_check_decrease_int_height 2 #774 #1910
[attach-var-names] #1908 (|prev| ; |Int|) (|cur| ; |Int|)
[mk-app] #1911 not #785
[mk-app] #1912 or #1911 #786
[mk-app] #1913 not #1912
[inst-discovered] theory-solving 0 basic# ; #788
[mk-app] #1914 = #788 #1913
[instance] 0 #1914
[attach-enode] #1914 0
[end-of-instance]
[mk-app] #1914 = #1912 #784
[mk-app] #1915 not #1914
[mk-app] #1916 = #784 #1913
[inst-discovered] theory-solving 0 basic# ; #1916
[mk-app] #1917 = #1916 #1915
[instance] 0 #1917
[attach-enode] #1917 0
[end-of-instance]
[mk-app] #1913 not #1912
[inst-discovered] theory-solving 0 basic# ; #1915
[mk-app] #1913 = #1915 #1915
[instance] 0 #1913
[attach-enode] #1913 0
[end-of-instance]
[mk-quant] #1913 prelude_height_lt 2 #790 #1915
[attach-var-names] #1913 (|y| ; |Height|) (|x| ; |Height|)
[mk-app] #1916 not #874
[mk-app] #1917 not #875
[mk-app] #1918 or #1916 #1917
[mk-app] #1919 not #1918
[inst-discovered] theory-solving 0 basic# ; #876
[mk-app] #1920 = #876 #1919
[instance] 0 #1920
[attach-enode] #1920 0
[end-of-instance]
[mk-app] #1920 or #878 #1919
[mk-app] #1921 not #881
[mk-app] #1922 not #882
[mk-app] #1923 not #883
[mk-app] #1924 not #884
[mk-app] #1925 not #885
[mk-app] #1926 not #886
[mk-app] #1927 not #887
[mk-app] #1928 not #888
[mk-app] #1929 not #889
[mk-app] #1930 not #890
[mk-app] #1931 not #891
[mk-app] #1932 not #892
[mk-app] #1933 not #893
[mk-app] #1934 not #894
[mk-app] #1935 not #895
[mk-app] #1936 not #896
[mk-app] #1937 not #897
[mk-app] #1938 not #898
[mk-app] #1939 not #899
[mk-app] #1940 not #900
[mk-app] #1941 not #901
[mk-app] #1942 not #902
[mk-app] #1943 not #903
[mk-app] #1944 not #904
[mk-app] #1945 not #905
[mk-app] #1946 or #1921 #1922 #1923 #1924 #1925 #1926 #1927 #1928 #1929 #1930 #1931 #1932 #1933 #1934 #1935 #1936 #1937 #1938 #1939 #1940 #1941 #1942 #1943 #1944 #1945
[mk-app] #1947 not #1946
[inst-discovered] theory-solving 0 basic# ; #906
[mk-app] #1948 = #906 #1947
[instance] 0 #1948
[attach-enode] #1948 0
[end-of-instance]
[mk-app] #1948 or #908 #1947
[inst-discovered] theory-solving 0 basic# ; #914
[mk-app] #1949 = #914 #914
[instance] 0 #1949
[attach-enode] #1949 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #919
[mk-app] #1949 = #919 #919
[instance] 0 #1949
[attach-enode] #1949 0
[end-of-instance]
[mk-app] #1949 not #964
[mk-app] #1950 not #965
[mk-app] #1951 or #1949 #1950
[mk-app] #1952 not #1951
[inst-discovered] theory-solving 0 basic# ; #966
[mk-app] #1953 = #966 #1952
[instance] 0 #1953
[attach-enode] #1953 0
[end-of-instance]
[mk-app] #1953 not #1952
[inst-discovered] theory-solving 0 basic# ; #1953
[mk-app] #1954 = #1953 #1951
[instance] 0 #1954
[attach-enode] #1954 0
[end-of-instance]
[mk-app] #1953 or #1949 #1950 #969
[mk-app] #1954 or #1951 #969
[inst-discovered] theory-solving 0 basic# ; #1954
[mk-app] #1955 = #1954 #1953
[instance] 0 #1955
[attach-enode] #1955 0
[end-of-instance]
[mk-quant] #1954 internal_the_q!types.Q./Q_constructor_definition 2 #971 #1953
[attach-var-names] #1954 (|_den!| ; |Int|) (|_num!| ; |Int|)
[mk-app] #1951 not #1025
[mk-app] #1952 not #1020
[mk-app] #1955 not #1027
[mk-app] #1956 or #1951 #1952 #1955
[mk-app] #1957 not #1956
[inst-discovered] theory-solving 0 basic# ; #1028
[mk-app] #1958 = #1028 #1957
[instance] 0 #1958
[attach-enode] #1958 0
[end-of-instance]
[mk-app] #1958 or #1032 #1957
[mk-quant] #1959 internal_core__ops__function__FnOnce_trait_type_bounds_definition 4 #1030 #1958
[attach-var-names] #1959 (|Args&| ; |Type|) (|Args&.| ; |Dcr|) (|Self%&| ; |Type|) (|Self%&.| ; |Dcr|)
[mk-app] #1960 or #1032 #1951 #1952
[mk-app] #1961 not #1960
[inst-discovered] theory-solving 0 basic# ; #1036
[mk-app] #1962 = #1036 #1961
[instance] 0 #1962
[attach-enode] #1962 0
[end-of-instance]
[mk-app] #1962 or #1040 #1961
[mk-quant] #1963 internal_core__ops__function__FnMut_trait_type_bounds_definition 4 #1038 #1962
[attach-var-names] #1963 (|Args&| ; |Type|) (|Args&.| ; |Dcr|) (|Self%&| ; |Type|) (|Self%&.| ; |Dcr|)
[mk-app] #1964 or #1040 #1951 #1952
[mk-app] #1965 not #1964
[inst-discovered] theory-solving 0 basic# ; #1044
[mk-app] #1966 = #1044 #1965
[instance] 0 #1966
[attach-enode] #1966 0
[end-of-instance]
[mk-app] #1966 or #1048 #1965
[mk-quant] #1967 internal_core__ops__function__Fn_trait_type_bounds_definition 4 #1046 #1966
[attach-var-names] #1967 (|Args&| ; |Type|) (|Args&.| ; |Dcr|) (|Self%&| ; |Type|) (|Self%&.| ; |Dcr|)
[mk-app] #1968 not #1054
[mk-app] #1969 not #1055
[mk-app] #1970 not #1056
[mk-app] #1971 or #1968 #1969 #1970
[mk-app] #1972 not #1971
[inst-discovered] theory-solving 0 basic# ; #1057
[mk-app] #1973 = #1057 #1972
[instance] 0 #1973
[attach-enode] #1973 0
[end-of-instance]
[mk-app] #1973 not #1972
[inst-discovered] theory-solving 0 basic# ; #1973
[mk-app] #1974 = #1973 #1971
[instance] 0 #1974
[attach-enode] #1974 0
[end-of-instance]
[mk-app] #1973 or #1968 #1969 #1970 #1061
[mk-app] #1974 or #1971 #1061
[inst-discovered] theory-solving 0 basic# ; #1974
[mk-app] #1975 = #1974 #1973
[instance] 0 #1975
[attach-enode] #1975 0
[end-of-instance]
[mk-quant] #1974 internal_proj____core!ops.function.FnOnce./Output_assoc_type_impl_true_definition 4 #1063 #1973
[attach-var-names] #1974 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #1971 or #1968 #1969 #1970
[mk-app] #1972 not #1971
[inst-discovered] theory-solving 0 basic# ; #1057
[mk-app] #1975 = #1057 #1972
[instance] 0 #1975
[attach-enode] #1975 0
[end-of-instance]
[mk-app] #1975 not #1972
[inst-discovered] theory-solving 0 basic# ; #1975
[mk-app] #1976 = #1975 #1971
[instance] 0 #1976
[attach-enode] #1976 0
[end-of-instance]
[mk-app] #1975 or #1968 #1969 #1970 #1070
[mk-app] #1976 or #1971 #1070
[inst-discovered] theory-solving 0 basic# ; #1976
[mk-app] #1977 = #1976 #1975
[instance] 0 #1977
[attach-enode] #1977 0
[end-of-instance]
[mk-quant] #1976 internal_proj__core!ops.function.FnOnce./Output_assoc_type_impl_false_definition 4 #1072 #1975
[attach-var-names] #1976 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #1971 not #1076
[mk-app] #1972 or #1968 #1969 #1971
[mk-app] #1977 not #1972
[inst-discovered] theory-solving 0 basic# ; #1077
[mk-app] #1978 = #1077 #1977
[instance] 0 #1978
[attach-enode] #1978 0
[end-of-instance]
[mk-app] #1978 not #1977
[inst-discovered] theory-solving 0 basic# ; #1978
[mk-app] #1979 = #1978 #1972
[instance] 0 #1979
[attach-enode] #1979 0
[end-of-instance]
[mk-app] #1978 or #1968 #1969 #1971 #1079
[mk-app] #1979 or #1972 #1079
[inst-discovered] theory-solving 0 basic# ; #1979
[mk-app] #1980 = #1979 #1978
[instance] 0 #1980
[attach-enode] #1980 0
[end-of-instance]
[mk-quant] #1979 internal_proj____core!ops.function.FnOnce./Output_assoc_type_impl_true_definition 4 #1081 #1978
[attach-var-names] #1979 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #1972 or #1968 #1969 #1971
[mk-app] #1977 not #1972
[inst-discovered] theory-solving 0 basic# ; #1077
[mk-app] #1980 = #1077 #1977
[instance] 0 #1980
[attach-enode] #1980 0
[end-of-instance]
[mk-app] #1980 not #1977
[inst-discovered] theory-solving 0 basic# ; #1980
[mk-app] #1981 = #1980 #1972
[instance] 0 #1981
[attach-enode] #1981 0
[end-of-instance]
[mk-app] #1980 or #1968 #1969 #1971 #1087
[mk-app] #1981 or #1972 #1087
[inst-discovered] theory-solving 0 basic# ; #1981
[mk-app] #1982 = #1981 #1980
[instance] 0 #1982
[attach-enode] #1982 0
[end-of-instance]
[mk-quant] #1981 internal_proj__core!ops.function.FnOnce./Output_assoc_type_impl_false_definition 4 #1089 #1980
[attach-var-names] #1981 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #1972 not #1095
[mk-app] #1977 not #1096
[mk-app] #1982 not #1097
[mk-app] #1983 or #1972 #1951 #1977 #1982 #1721
[mk-app] #1984 not #1983
[inst-discovered] theory-solving 0 basic# ; #1098
[mk-app] #1985 = #1098 #1984
[instance] 0 #1985
[attach-enode] #1985 0
[end-of-instance]
[mk-app] #1985 not #1984
[inst-discovered] theory-solving 0 basic# ; #1985
[mk-app] #1986 = #1985 #1983
[instance] 0 #1986
[attach-enode] #1986 0
[end-of-instance]
[mk-app] #1985 or #1972 #1951 #1977 #1982 #1721 #1102
[mk-app] #1986 or #1983 #1102
[inst-discovered] theory-solving 0 basic# ; #1986
[mk-app] #1987 = #1986 #1985
[instance] 0 #1987
[attach-enode] #1987 0
[end-of-instance]
[mk-quant] #1986 internal_proj____core!ops.function.FnOnce./Output_assoc_type_impl_true_definition 6 #1104 #1985
[attach-var-names] #1986 (|A&| ; |Type|) (|A&.| ; |Dcr|) (|F&| ; |Type|) (|F&.| ; |Dcr|) (|Args&| ; |Type|) (|Args&.| ; |Dcr|)
[mk-app] #1983 or #1972 #1951 #1977 #1982 #1721
[mk-app] #1984 not #1983
[inst-discovered] theory-solving 0 basic# ; #1098
[mk-app] #1987 = #1098 #1984
[instance] 0 #1987
[attach-enode] #1987 0
[end-of-instance]
[mk-app] #1987 not #1984
[inst-discovered] theory-solving 0 basic# ; #1987
[mk-app] #1988 = #1987 #1983
[instance] 0 #1988
[attach-enode] #1988 0
[end-of-instance]
[mk-app] #1987 or #1972 #1951 #1977 #1982 #1721 #1111
[mk-app] #1988 or #1983 #1111
[inst-discovered] theory-solving 0 basic# ; #1988
[mk-app] #1989 = #1988 #1987
[instance] 0 #1989
[attach-enode] #1989 0
[end-of-instance]
[mk-quant] #1988 internal_proj__core!ops.function.FnOnce./Output_assoc_type_impl_false_definition 6 #1113 #1987
[attach-var-names] #1988 (|A&| ; |Type|) (|A&.| ; |Dcr|) (|F&| ; |Type|) (|F&.| ; |Dcr|) (|Args&| ; |Type|) (|Args&.| ; |Dcr|)
[mk-app] #1983 or #1968 #1969 #1971
[mk-app] #1984 not #1983
[inst-discovered] theory-solving 0 basic# ; #1077
[mk-app] #1989 = #1077 #1984
[instance] 0 #1989
[attach-enode] #1989 0
[end-of-instance]
[mk-app] #1989 not #1984
[inst-discovered] theory-solving 0 basic# ; #1989
[mk-app] #1990 = #1989 #1983
[instance] 0 #1990
[attach-enode] #1990 0
[end-of-instance]
[mk-app] #1989 or #1968 #1969 #1971 #1117
[mk-app] #1990 or #1983 #1117
[inst-discovered] theory-solving 0 basic# ; #1990
[mk-app] #1991 = #1990 #1989
[instance] 0 #1991
[attach-enode] #1991 0
[end-of-instance]
[mk-quant] #1990 internal_core__ops__function__impls__impl&__4_trait_impl_definition 4 #1119 #1989
[attach-var-names] #1990 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #1983 not #1125
[mk-app] #1984 not #1126
[mk-app] #1991 or #1983 #1984
[mk-app] #1992 not #1991
[inst-discovered] theory-solving 0 basic# ; #1127
[mk-app] #1993 = #1127 #1992
[instance] 0 #1993
[attach-enode] #1993 0
[end-of-instance]
[mk-app] #1993 not #1992
[inst-discovered] theory-solving 0 basic# ; #1993
[mk-app] #1994 = #1993 #1991
[instance] 0 #1994
[attach-enode] #1994 0
[end-of-instance]
[mk-app] #1993 not #1130
[mk-app] #1994 not #1133
[mk-app] #1995 or #1972 #1968 #1977 #1993 #1994
[mk-app] #1996 not #1995
[inst-discovered] theory-solving 0 basic# ; #1141
[mk-app] #1997 = #1141 #1996
[instance] 0 #1997
[attach-enode] #1997 0
[end-of-instance]
[mk-app] #1997 not #1996
[inst-discovered] theory-solving 0 basic# ; #1997
[mk-app] #1998 = #1997 #1995
[instance] 0 #1998
[attach-enode] #1998 0
[end-of-instance]
[mk-app] #1996 or #1983 #1984 #1972 #1968 #1977 #1993 #1994 #1135
[mk-app] #1997 or #1991 #1995 #1135
[inst-discovered] theory-solving 0 basic# ; #1997
[mk-app] #1998 = #1997 #1996
[instance] 0 #1998
[attach-enode] #1998 0
[end-of-instance]
[mk-quant] #1995 user_vstd__function__axiom_fn_mut_call_requires_0 6 #1138 #1996
[attach-var-names] #1995 (|args!| ; |Poly|) (|f!| ; |Poly|) (|F&| ; |Type|) (|F&.| ; |Dcr|) (|Args&| ; |Type|) (|Args&.| ; |Dcr|)
[mk-app] #1991 or #1146 #1995
[mk-app] #1992 not #1154
[mk-app] #1997 not #1155
[mk-app] #1998 not #1157
[mk-app] #1999 or #1992 #1997 #1998
[mk-app] #2000 not #1999
[inst-discovered] theory-solving 0 basic# ; #1158
[mk-app] #2001 = #1158 #2000
[instance] 0 #2001
[attach-enode] #2001 0
[end-of-instance]
[mk-app] #2001 not #2000
[inst-discovered] theory-solving 0 basic# ; #2001
[mk-app] #2002 = #2001 #1999
[instance] 0 #2002
[attach-enode] #2002 0
[end-of-instance]
[mk-app] #2001 not #1159
[mk-app] #2002 not #1160
[mk-app] #2003 not #1162
[mk-app] #2004 not #1164
[mk-app] #2005 not #1166
[mk-app] #2006 or #2001 #2002 #2003 #2004 #2005
[mk-app] #2007 not #2006
[inst-discovered] theory-solving 0 basic# ; #1176
[mk-app] #2008 = #1176 #2007
[instance] 0 #2008
[attach-enode] #2008 0
[end-of-instance]
[mk-app] #2008 not #2007
[inst-discovered] theory-solving 0 basic# ; #2008
[mk-app] #2009 = #2008 #2006
[instance] 0 #2009
[attach-enode] #2009 0
[end-of-instance]
[mk-app] #2007 not #1168
[mk-app] #2008 not #1169
[mk-app] #2009 or #2007 #2008
[mk-app] #2010 not #2009
[inst-discovered] theory-solving 0 basic# ; #1170
[mk-app] #2011 = #1170 #2010
[instance] 0 #2011
[attach-enode] #2011 0
[end-of-instance]
[mk-app] #2011 or #1992 #1997 #1998 #2001 #2002 #2003 #2004 #2005 #2010
[mk-app] #2012 or #1999 #2006 #2010
[inst-discovered] theory-solving 0 basic# ; #2012
[mk-app] #2013 = #2012 #2011
[instance] 0 #2013
[attach-enode] #2013 0
[end-of-instance]
[mk-quant] #2006 user_vstd__function__axiom_fn_mut_call_ensures_1 7 #1173 #2011
[attach-var-names] #2006 (|output!| ; |Poly|) (|args!| ; |Poly|) (|f!| ; |Poly|) (|F&| ; |Type|) (|F&.| ; |Dcr|) (|Args&| ; |Type|) (|Args&.| ; |Dcr|)
[mk-app] #1999 or #1181 #2006
[mk-app] #2000 not #1801
[mk-app] #2012 not #1800
[mk-app] #2013 or #2000 #2012
[mk-app] #2014 not #2013
[inst-discovered] theory-solving 0 basic# ; #1802
[mk-app] #2015 = #1802 #2014
[instance] 0 #2015
[attach-enode] #2015 0
[end-of-instance]
[mk-quant] #2015 internal_the_q!model.divides.?_definition 2 #1262 #2014
[attach-var-names] #2015 (|n!| ; |Poly|) (|d!| ; |Poly|)
[mk-app] #2016 or #1265 #2015
[mk-app] #2017 not #1273
[mk-app] #2018 or #2017 #1207
[mk-app] #2019 not #2018
[inst-discovered] theory-solving 0 basic# ; #1274
[mk-app] #2020 = #1274 #2019
[instance] 0 #2020
[attach-enode] #2020 0
[end-of-instance]
[mk-app] #2020 not #2019
[inst-discovered] theory-solving 0 basic# ; #2020
[mk-app] #2021 = #2020 #2018
[instance] 0 #2021
[attach-enode] #2021 0
[end-of-instance]
[mk-app] #2020 or #2017 #1207 #1280
[mk-app] #2021 or #2018 #1280
[inst-discovered] theory-solving 0 basic# ; #2021
[mk-app] #2022 = #2021 #2020
[instance] 0 #2022
[attach-enode] #2022 0
[end-of-instance]
[mk-quant] #2021 internal_the_q!model.gcd_nat._fuel_to_body_definition 3 #1282 #2020
[attach-var-names] #2021 (|fuel%| ; |Fuel|) (|b!| ; |Poly|) (|a!| ; |Poly|)
[mk-app] #2018 or #1207 #201
[mk-app] #2019 not #2018
[inst-discovered] theory-solving 0 basic# ; #1288
[mk-app] #2022 = #1288 #2019
[instance] 0 #2022
[attach-enode] #2022 0
[end-of-instance]
[mk-app] #2022 not #2019
[inst-discovered] theory-solving 0 basic# ; #2022
[mk-app] #2023 = #2022 #2018
[instance] 0 #2023
[attach-enode] #2023 0
[end-of-instance]
[mk-app] #2022 or #1207 #201 #1293
[mk-app] #2023 or #2018 #1293
[inst-discovered] theory-solving 0 basic# ; #2023
[mk-app] #2024 = #2023 #2022
[instance] 0 #2024
[attach-enode] #2024 0
[end-of-instance]
[mk-quant] #2023 internal_the_q!model.gcd_nat.?_definition 2 #1295 #2022
[attach-var-names] #2023 (|b!| ; |Poly|) (|a!| ; |Poly|)
[mk-app] #2018 or #1301 #2023
[mk-app] #2019 or #1207 #201
[mk-app] #2024 not #2019
[inst-discovered] theory-solving 0 basic# ; #1288
[mk-app] #2025 = #1288 #2024
[instance] 0 #2025
[attach-enode] #2025 0
[end-of-instance]
[mk-app] #2025 not #2024
[inst-discovered] theory-solving 0 basic# ; #2025
[mk-app] #2026 = #2025 #2019
[instance] 0 #2026
[attach-enode] #2026 0
[end-of-instance]
[mk-app] #2025 or #1207 #201 #1307
[mk-app] #2026 or #2019 #1307
[inst-discovered] theory-solving 0 basic# ; #2026
[mk-app] #2027 = #2026 #2025
[instance] 0 #2027
[attach-enode] #2027 0
[end-of-instance]
[mk-quant] #2026 internal_the_q!model.gcd_nat.?_pre_post_definition 2 #1295 #2025
[attach-var-names] #2026 (|b!| ; |Poly|) (|a!| ; |Poly|)
[mk-app] #2019 or #2017 #1207
[mk-app] #2024 not #2019
[inst-discovered] theory-solving 0 basic# ; #1274
[mk-app] #2027 = #1274 #2024
[instance] 0 #2027
[attach-enode] #2027 0
[end-of-instance]
[mk-app] #2027 not #2024
[inst-discovered] theory-solving 0 basic# ; #2027
[mk-app] #2028 = #2027 #2019
[instance] 0 #2028
[attach-enode] #2028 0
[end-of-instance]
[mk-app] #2027 or #2017 #1207 #1313
[mk-app] #2028 or #2019 #1313
[inst-discovered] theory-solving 0 basic# ; #2028
[mk-app] #2029 = #2028 #2027
[instance] 0 #2029
[attach-enode] #2029 0
[end-of-instance]
[mk-quant] #2028 internal_the_q!model.rec__gcd_nat.?_pre_post_rec_definition 3 #1271 #2027
[attach-var-names] #2028 (|fuel%| ; |Fuel|) (|b!| ; |Poly|) (|a!| ; |Poly|)
[mk-app] #2019 not #1410
[mk-app] #2024 not #1412
[mk-app] #2029 or #2019 #2024
[mk-app] #2030 not #2029
[inst-discovered] theory-solving 0 basic# ; #1413
[mk-app] #2031 = #1413 #2030
[instance] 0 #2031
[attach-enode] #2031 0
[end-of-instance]
[mk-app] #2031 = #2029 #1398
[mk-app] #2032 not #2031
[mk-app] #2033 = #1398 #2030
[inst-discovered] theory-solving 0 basic# ; #2033
[mk-app] #2034 = #2033 #2032
[instance] 0 #2034
[attach-enode] #2034 0
[end-of-instance]
[mk-app] #2030 not #2029
[inst-discovered] theory-solving 0 basic# ; #2032
[mk-app] #2030 = #2032 #2032
[instance] 0 #2030
[attach-enode] #2030 0
[end-of-instance]
[mk-quant] #2030 internal_the_q!model.fits_budget.?_definition 2 #1405 #2032
[attach-var-names] #2030 (|d!| ; |Poly|) (|n!| ; |Poly|)
[mk-app] #2033 or #1416 #2030
[mk-app] #2034 not #1441
[mk-app] #2035 not #1459
[mk-app] #2036 not #1460
[mk-app] #2037 not #1464
[mk-app] #2038 or #1456 #2034 #2035 #2036 #2037
[mk-app] #2039 not #2038
[inst-discovered] theory-solving 0 basic# ; #1465
[mk-app] #2040 = #1465 #2039
[instance] 0 #2040
[attach-enode] #2040 0
[end-of-instance]
[mk-app] #2040 = #2038 #1436
[mk-app] #2041 not #2040
[mk-app] #2042 = #1436 #2039
[inst-discovered] theory-solving 0 basic# ; #2042
[mk-app] #2043 = #2042 #2041
[instance] 0 #2043
[attach-enode] #2043 0
[end-of-instance]
[mk-app] #2039 not #2038
[inst-discovered] theory-solving 0 basic# ; #2041
[mk-app] #2039 = #2041 #2041
[instance] 0 #2039
[attach-enode] #2039 0
[end-of-instance]
[mk-quant] #2039 internal_the_q!model.impl&__0.wf.?_definition 1 #1453 #2041
[attach-var-names] #2039 (|self!| ; |Poly|)
[mk-app] #2042 or #1468 #2039
[mk-app] #2043 not #1527
[inst-discovered] theory-solving 0 basic# ; #1530
[mk-app] #2043 = #1530 #1530
[instance] 0 #2043
[attach-enode] #2043 0
[end-of-instance]
[mk-app] #2043 or #1968 #1969 #1970
[mk-app] #2044 not #2043
[inst-discovered] theory-solving 0 basic# ; #1057
[mk-app] #2045 = #1057 #2044
[instance] 0 #2045
[attach-enode] #2045 0
[end-of-instance]
[mk-app] #2045 not #2044
[inst-discovered] theory-solving 0 basic# ; #2045
[mk-app] #2046 = #2045 #2043
[instance] 0 #2046
[attach-enode] #2046 0
[end-of-instance]
[mk-app] #2045 or #1968 #1969 #1970 #1670
[mk-app] #2046 or #2043 #1670
[inst-discovered] theory-solving 0 basic# ; #2046
[mk-app] #2047 = #2046 #2045
[instance] 0 #2047
[attach-enode] #2047 0
[end-of-instance]
[mk-quant] #2046 internal_core__ops__function__impls__impl&__2_trait_impl_definition 4 #1672 #2045
[attach-var-names] #2046 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #2043 or #1968 #1969 #1970
[mk-app] #2044 not #2043
[inst-discovered] theory-solving 0 basic# ; #1057
[mk-app] #2047 = #1057 #2044
[instance] 0 #2047
[attach-enode] #2047 0
[end-of-instance]
[mk-app] #2047 not #2044
[inst-discovered] theory-solving 0 basic# ; #2047
[mk-app] #2048 = #2047 #2043
[instance] 0 #2048
[attach-enode] #2048 0
[end-of-instance]
[mk-app] #2047 or #1968 #1969 #1970 #1676
[mk-app] #2048 or #2043 #1676
[inst-discovered] theory-solving 0 basic# ; #2048
[mk-app] #2049 = #2048 #2047
[instance] 0 #2049
[attach-enode] #2049 0
[end-of-instance]
[mk-quant] #2048 internal_core__ops__function__impls__impl&__1_trait_impl_definition 4 #1678 #2047
[attach-var-names] #2048 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #2043 or #1968 #1969 #1970
[mk-app] #2044 not #2043
[inst-discovered] theory-solving 0 basic# ; #1057
[mk-app] #2049 = #1057 #2044
[instance] 0 #2049
[attach-enode] #2049 0
[end-of-instance]
[mk-app] #2049 not #2044
[inst-discovered] theory-solving 0 basic# ; #2049
[mk-app] #2050 = #2049 #2043
[instance] 0 #2050
[attach-enode] #2050 0
[end-of-instance]
[mk-app] #2049 or #1968 #1969 #1970 #1682
[mk-app] #2050 or #2043 #1682
[inst-discovered] theory-solving 0 basic# ; #2050
[mk-app] #2051 = #2050 #2049
[instance] 0 #2051
[attach-enode] #2051 0
[end-of-instance]
[mk-quant] #2050 internal_core__ops__function__impls__impl&__0_trait_impl_definition 4 #1684 #2049
[attach-var-names] #2050 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #2043 or #1972 #1951 #1977 #1982 #1721
[mk-app] #2044 not #2043
[inst-discovered] theory-solving 0 basic# ; #1098
[mk-app] #2051 = #1098 #2044
[instance] 0 #2051
[attach-enode] #2051 0
[end-of-instance]
[mk-app] #2051 not #2044
[inst-discovered] theory-solving 0 basic# ; #2051
[mk-app] #2052 = #2051 #2043
[instance] 0 #2052
[attach-enode] #2052 0
[end-of-instance]
[mk-app] #2051 or #1972 #1951 #1977 #1982 #1721 #1688
[mk-app] #2052 or #2043 #1688
[inst-discovered] theory-solving 0 basic# ; #2052
[mk-app] #2053 = #2052 #2051
[instance] 0 #2053
[attach-enode] #2053 0
[end-of-instance]
[mk-quant] #2052 internal_alloc__boxed__impl&__31_trait_impl_definition 6 #1690 #2051
[attach-var-names] #2052 (|A&| ; |Type|) (|A&.| ; |Dcr|) (|F&| ; |Type|) (|F&.| ; |Dcr|) (|Args&| ; |Type|) (|Args&.| ; |Dcr|)
[mk-app] #2043 or #1972 #1951 #1977 #1993 #1721
[mk-app] #2044 not #2043
[inst-discovered] theory-solving 0 basic# ; #1694
[mk-app] #2053 = #1694 #2044
[instance] 0 #2053
[attach-enode] #2053 0
[end-of-instance]
[mk-app] #2053 not #2044
[inst-discovered] theory-solving 0 basic# ; #2053
[mk-app] #2054 = #2053 #2043
[instance] 0 #2054
[attach-enode] #2054 0
[end-of-instance]
[mk-app] #2053 or #1972 #1951 #1977 #1993 #1721 #1695
[mk-app] #2054 or #2043 #1695
[inst-discovered] theory-solving 0 basic# ; #2054
[mk-app] #2055 = #2054 #2053
[instance] 0 #2055
[attach-enode] #2055 0
[end-of-instance]
[mk-quant] #2054 internal_alloc__boxed__impl&__32_trait_impl_definition 6 #1697 #2053
[attach-var-names] #2054 (|A&| ; |Type|) (|A&.| ; |Dcr|) (|F&| ; |Type|) (|F&.| ; |Dcr|) (|Args&| ; |Type|) (|Args&.| ; |Dcr|)
[mk-app] #2043 not #1702
[mk-app] #2044 or #1972 #1951 #1977 #2043 #1721
[mk-app] #2055 not #2044
[inst-discovered] theory-solving 0 basic# ; #1703
[mk-app] #2056 = #1703 #2055
[instance] 0 #2056
[attach-enode] #2056 0
[end-of-instance]
[mk-app] #2056 not #2055
[inst-discovered] theory-solving 0 basic# ; #2056
[mk-app] #2057 = #2056 #2044
[instance] 0 #2057
[attach-enode] #2057 0
[end-of-instance]
[mk-app] #2056 or #1972 #1951 #1977 #2043 #1721 #1704
[mk-app] #2057 or #2044 #1704
[inst-discovered] theory-solving 0 basic# ; #2057
[mk-app] #2058 = #2057 #2056
[instance] 0 #2058
[attach-enode] #2058 0
[end-of-instance]
[mk-quant] #2057 internal_alloc__boxed__impl&__33_trait_impl_definition 6 #1706 #2056
[attach-var-names] #2057 (|A&| ; |Type|) (|A&.| ; |Dcr|) (|F&| ; |Type|) (|F&.| ; |Dcr|) (|Args&| ; |Type|) (|Args&.| ; |Dcr|)
[mk-app] #2044 or #1968 #1969 #1971
[mk-app] #2055 not #2044
[inst-discovered] theory-solving 0 basic# ; #1077
[mk-app] #2058 = #1077 #2055
[instance] 0 #2058
[attach-enode] #2058 0
[end-of-instance]
[mk-app] #2058 not #2055
[inst-discovered] theory-solving 0 basic# ; #2058
[mk-app] #2059 = #2058 #2044
[instance] 0 #2059
[attach-enode] #2059 0
[end-of-instance]
[mk-app] #2058 or #1968 #1969 #1971 #1711
[mk-app] #2059 or #2044 #1711
[inst-discovered] theory-solving 0 basic# ; #2059
[mk-app] #2060 = #2059 #2058
[instance] 0 #2060
[attach-enode] #2060 0
[end-of-instance]
[mk-quant] #2059 internal_core__ops__function__impls__impl&__3_trait_impl_definition 4 #1713 #2058
[attach-var-names] #2059 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #2044 not #1730
[mk-app] #2055 or #1951 #2044 #1721
[mk-app] #2060 not #2055
[inst-discovered] theory-solving 0 basic# ; #1731
[mk-app] #2061 = #1731 #2060
[instance] 0 #2061
[attach-enode] #2061 0
[end-of-instance]
[mk-app] #2061 not #2060
[inst-discovered] theory-solving 0 basic# ; #2061
[mk-app] #2062 = #2061 #2055
[instance] 0 #2062
[attach-enode] #2062 0
[end-of-instance]
[mk-app] #2061 or #1951 #2044 #1721 #1732
[mk-app] #2062 or #2055 #1732
[inst-discovered] theory-solving 0 basic# ; #2062
[mk-app] #2063 = #2062 #2061
[instance] 0 #2063
[attach-enode] #2063 0
[end-of-instance]
[mk-quant] #2062 internal_alloc__boxed__impl&__49_trait_impl_definition 4 #1734 #2061
[attach-var-names] #2062 (|A&| ; |Type|) (|A&.| ; |Dcr|) (|T&| ; |Type|) (|T&.| ; |Dcr|)
[mk-app] #2055 or #1951 #2044 #1721
[mk-app] #2060 not #2055
[inst-discovered] theory-solving 0 basic# ; #1731
[mk-app] #2063 = #1731 #2060
[instance] 0 #2063
[attach-enode] #2063 0
[end-of-instance]
[mk-app] #2063 not #2060
[inst-discovered] theory-solving 0 basic# ; #2063
[mk-app] #2064 = #2063 #2055
[instance] 0 #2064
[attach-enode] #2064 0
[end-of-instance]
[mk-app] #2063 or #1951 #2044 #1721 #1740
[mk-app] #2064 or #2055 #1740
[inst-discovered] theory-solving 0 basic# ; #2064
[mk-app] #2065 = #2064 #2063
[instance] 0 #2065
[attach-enode] #2065 0
[end-of-instance]
[mk-quant] #2064 internal_alloc__rc__impl&__115_trait_impl_definition 4 #1742 #2063
[attach-var-names] #2064 (|A&| ; |Type|) (|A&.| ; |Dcr|) (|T&| ; |Type|) (|T&.| ; |Dcr|)
[mk-app] #2055 or #1951 #2044 #1721
[mk-app] #2060 not #2055
[inst-discovered] theory-solving 0 basic# ; #1731
[mk-app] #2065 = #1731 #2060
[instance] 0 #2065
[attach-enode] #2065 0
[end-of-instance]
[mk-app] #2065 not #2060
[inst-discovered] theory-solving 0 basic# ; #2065
[mk-app] #2066 = #2065 #2055
[instance] 0 #2066
[attach-enode] #2066 0
[end-of-instance]
[mk-app] #2065 or #1951 #2044 #1721 #1747
[mk-app] #2066 or #2055 #1747
[inst-discovered] theory-solving 0 basic# ; #2066
[mk-app] #2067 = #2066 #2065
[instance] 0 #2067
[attach-enode] #2067 0
[end-of-instance]
[mk-quant] #2066 internal_alloc__sync__impl&__117_trait_impl_definition 4 #1749 #2065
[attach-var-names] #2066 (|A&| ; |Type|) (|A&.| ; |Dcr|) (|T&| ; |Type|) (|T&.| ; |Dcr|)
[mk-app] #2055 not #1759
[inst-discovered] theory-solving 0 basic# ; #1762
[mk-app] #2055 = #1762 #1762
[instance] 0 #2055
[attach-enode] #2055 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1808
[mk-app] #1736 = #1808 #1808
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1820
[mk-app] #1736 = #1820 #1820
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1823
[mk-app] #1736 = #1823 #1823
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1827
[mk-app] #1736 = #1827 #1827
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1830
[mk-app] #1736 = #1830 #1830
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1833
[mk-app] #1736 = #1833 #1833
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1837
[mk-app] #1736 = #1837 #1837
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1841
[mk-app] #1736 = #1841 #1841
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1845
[mk-app] #1736 = #1845 #1845
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[mk-app] #1736 not #1855
[inst-discovered] theory-solving 0 basic# ; #1858
[mk-app] #1736 = #1858 #1858
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[mk-app] #1736 not #1856
[inst-discovered] theory-solving 0 basic# ; #1862
[mk-app] #1736 = #1862 #1862
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1841
[mk-app] #1736 = #1841 #1841
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1845
[mk-app] #1736 = #1845 #1845
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1867
[mk-app] #1736 = #1867 #1867
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1873
[mk-app] #1736 = #1873 #1873
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1878
[mk-app] #1736 = #1878 #1878
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1883
[mk-app] #1736 = #1883 #1883
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1887
[mk-app] #1736 = #1887 #1887
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1889
[mk-app] #1736 = #1889 #1889
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1891
[mk-app] #1736 = #1891 #1891
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1893
[mk-app] #1736 = #1893 #1893
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1895
[mk-app] #1736 = #1895 #1895
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1897
[mk-app] #1736 = #1897 #1897
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1899
[mk-app] #1736 = #1899 #1899
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1902
[mk-app] #1736 = #1902 #1902
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1904
[mk-app] #1736 = #1904 #1904
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[mk-app] #1736 not #1907
[inst-discovered] theory-solving 0 basic# ; #1910
[mk-app] #1736 = #1910 #1910
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[mk-app] #1736 not #1912
[inst-discovered] theory-solving 0 basic# ; #1915
[mk-app] #1736 = #1915 #1915
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1918
[mk-app] #1736 = #1918 #1918
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1946
[mk-app] #1736 = #1946 #1946
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #914
[mk-app] #1736 = #914 #914
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #919
[mk-app] #1736 = #919 #919
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1953
[mk-app] #1736 = #1953 #1953
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1960
[mk-app] #1736 = #1960 #1960
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1964
[mk-app] #1736 = #1964 #1964
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1985
[mk-app] #1736 = #1985 #1985
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1987
[mk-app] #1736 = #1987 #1987
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1996
[mk-app] #1736 = #1996 #1996
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2009
[mk-app] #1736 = #2009 #2009
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2011
[mk-app] #1736 = #2011 #2011
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2020
[mk-app] #1736 = #2020 #2020
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2022
[mk-app] #1736 = #2022 #2022
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2025
[mk-app] #1736 = #2025 #2025
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2027
[mk-app] #1736 = #2027 #2027
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2029
[mk-app] #1736 = #2029 #2029
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[mk-app] #1736 not #2029
[inst-discovered] theory-solving 0 basic# ; #2032
[mk-app] #1736 = #2032 #2032
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2038
[mk-app] #1736 = #2038 #2038
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[mk-app] #1736 not #2038
[inst-discovered] theory-solving 0 basic# ; #2041
[mk-app] #1736 = #2041 #2041
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[mk-app] #1736 not #1527
[inst-discovered] theory-solving 0 basic# ; #1530
[mk-app] #1736 = #1530 #1530
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2051
[mk-app] #1736 = #2051 #2051
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2053
[mk-app] #1736 = #2053 #2053
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2056
[mk-app] #1736 = #2056 #2056
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2061
[mk-app] #1736 = #2061 #2061
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2063
[mk-app] #1736 = #2063 #2063
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2065
[mk-app] #1736 = #2065 #2065
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[mk-app] #1736 not #1759
[inst-discovered] theory-solving 0 basic# ; #1762
[mk-app] #1736 = #1762 #1762
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1808
[mk-app] #1736 = #1808 #1808
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1820
[mk-app] #1736 = #1820 #1820
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1823
[mk-app] #1736 = #1823 #1823
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1827
[mk-app] #1736 = #1827 #1827
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1830
[mk-app] #1736 = #1830 #1830
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1833
[mk-app] #1736 = #1833 #1833
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1837
[mk-app] #1736 = #1837 #1837
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1841
[mk-app] #1736 = #1841 #1841
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1845
[mk-app] #1736 = #1845 #1845
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[mk-app] #1736 not #1855
[inst-discovered] theory-solving 0 basic# ; #1858
[mk-app] #1736 = #1858 #1858
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[mk-app] #1736 not #1856
[inst-discovered] theory-solving 0 basic# ; #1862
[mk-app] #1736 = #1862 #1862
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1841
[mk-app] #1736 = #1841 #1841
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1845
[mk-app] #1736 = #1845 #1845
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1867
[mk-app] #1736 = #1867 #1867
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1873
[mk-app] #1736 = #1873 #1873
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1878
[mk-app] #1736 = #1878 #1878
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1883
[mk-app] #1736 = #1883 #1883
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1887
[mk-app] #1736 = #1887 #1887
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1889
[mk-app] #1736 = #1889 #1889
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1891
[mk-app] #1736 = #1891 #1891
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1893
[mk-app] #1736 = #1893 #1893
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1895
[mk-app] #1736 = #1895 #1895
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1897
[mk-app] #1736 = #1897 #1897
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1899
[mk-app] #1736 = #1899 #1899
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1902
[mk-app] #1736 = #1902 #1902
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1904
[mk-app] #1736 = #1904 #1904
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[mk-app] #1736 not #1907
[inst-discovered] theory-solving 0 basic# ; #1910
[mk-app] #1736 = #1910 #1910
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[mk-app] #1736 not #1912
[inst-discovered] theory-solving 0 basic# ; #1915
[mk-app] #1736 = #1915 #1915
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #914
[mk-app] #1736 = #914 #914
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #919
[mk-app] #1736 = #919 #919
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1953
[mk-app] #1736 = #1953 #1953
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1960
[mk-app] #1736 = #1960 #1960
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1964
[mk-app] #1736 = #1964 #1964
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1985
[mk-app] #1736 = #1985 #1985
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1987
[mk-app] #1736 = #1987 #1987
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1996
[mk-app] #1736 = #1996 #1996
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2009
[mk-app] #1736 = #2009 #2009
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2011
[mk-app] #1736 = #2011 #2011
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2020
[mk-app] #1736 = #2020 #2020
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2022
[mk-app] #1736 = #2022 #2022
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2025
[mk-app] #1736 = #2025 #2025
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2027
[mk-app] #1736 = #2027 #2027
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2029
[mk-app] #1736 = #2029 #2029
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[mk-app] #1736 not #2029
[inst-discovered] theory-solving 0 basic# ; #2032
[mk-app] #1736 = #2032 #2032
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2038
[mk-app] #1736 = #2038 #2038
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[mk-app] #1736 not #2038
[inst-discovered] theory-solving 0 basic# ; #2041
[mk-app] #1736 = #2041 #2041
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[mk-app] #1736 not #1527
[inst-discovered] theory-solving 0 basic# ; #1530
[mk-app] #1736 = #1530 #1530
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2051
[mk-app] #1736 = #2051 #2051
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2053
[mk-app] #1736 = #2053 #2053
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2056
[mk-app] #1736 = #2056 #2056
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2061
[mk-app] #1736 = #2061 #2061
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2063
[mk-app] #1736 = #2063 #2063
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2065
[mk-app] #1736 = #2065 #2065
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[mk-app] #1736 not #1759
[inst-discovered] theory-solving 0 basic# ; #1762
[mk-app] #1736 = #1762 #1762
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[mk-app] #1736 or #878 #874
[mk-app] #1751 or #878 #875
[mk-app] #1752 or #908 #881
[mk-app] #1744 or #908 #882
[mk-app] #1745 or #908 #883
[mk-app] #1737 or #908 #884
[mk-app] #1738 or #908 #885
[mk-app] #1083 or #908 #886
[mk-app] #1715 or #908 #887
[mk-app] #1716 or #908 #888
[mk-app] #1708 or #908 #889
[mk-app] #1709 or #908 #890
[mk-app] #1710 or #908 #891
[mk-app] #1699 or #908 #892
[mk-app] #1700 or #908 #893
[mk-app] #1701 or #908 #894
[mk-app] #1106 or #908 #895
[mk-app] #1692 or #908 #896
[mk-app] #1693 or #908 #897
[mk-app] #1065 or #908 #898
[mk-app] #1686 or #908 #899
[mk-app] #1687 or #908 #900
[mk-app] #1680 or #908 #901
[mk-app] #1681 or #908 #902
[mk-app] #1674 or #908 #903
[mk-app] #1675 or #908 #904
[mk-app] #1457 or #908 #905
[assign] #39 justification -1: 
[assign] #43 justification -1: 
[assign] #56 justification -1: 
[assign] #63 justification -1: 
[assign] #1809 justification -1: 
[assign] #88 justification -1: 
[assign] #92 justification -1: 
[assign] #96 justification -1: 
[assign] #100 justification -1: 
[assign] #104 justification -1: 
[assign] #108 justification -1: 
[assign] #112 justification -1: 
[assign] #116 justification -1: 
[assign] #120 justification -1: 
[attach-enode] #121 0
[attach-enode] #122 0
[assign] #122 justification -1: 
[assign] #128 justification -1: 
[assign] #134 justification -1: 
[assign] #139 justification -1: 
[assign] #144 justification -1: 
[assign] #1812 justification -1: 
[assign] #161 justification -1: 
[assign] #165 justification -1: 
[assign] #170 justification -1: 
[assign] #174 justification -1: 
[assign] #184 justification -1: 
[assign] #195 justification -1: 
[assign] #203 justification -1: 
[assign] #211 justification -1: 
[assign] #219 justification -1: 
[assign] #228 justification -1: 
[assign] #236 justification -1: 
[assign] #244 justification -1: 
[assign] #252 justification -1: 
[assign] #262 justification -1: 
[assign] #269 justification -1: 
[attach-enode] #270 0
[attach-enode] #271 0
[attach-enode] #272 0
[attach-enode] #273 0
[attach-enode] #274 0
[attach-enode] #276 0
[attach-enode] #277 0
[attach-enode] #278 0
[attach-enode] #279 0
[assign] #279 justification -1: 
[attach-enode] #280 0
[attach-enode] #281 0
[attach-enode] #282 0
[attach-enode] #283 0
[assign] #283 justification -1: 
[attach-enode] #284 0
[attach-enode] #285 0
[attach-enode] #286 0
[assign] #286 justification -1: 
[attach-enode] #287 0
[attach-enode] #288 0
[attach-enode] #289 0
[assign] #289 justification -1: 
[attach-enode] #290 0
[attach-enode] #291 0
[attach-enode] #296 0
[attach-enode] #297 0
[assign] #297 justification -1: 
[attach-enode] #298 0
[attach-enode] #301 0
[attach-enode] #302 0
[assign] #302 justification -1: 
[attach-enode] #303 0
[attach-enode] #307 0
[attach-enode] #308 0
[assign] #308 justification -1: 
[attach-enode] #309 0
[attach-enode] #313 0
[attach-enode] #314 0
[assign] #314 justification -1: 
[attach-enode] #315 0
[attach-enode] #319 0
[attach-enode] #320 0
[assign] #320 justification -1: 
[attach-enode] #321 0
[attach-enode] #325 0
[attach-enode] #326 0
[assign] #326 justification -1: 
[attach-enode] #327 0
[attach-enode] #328 0
[assign] #328 justification -1: 
[attach-enode] #329 0
[attach-enode] #304 0
[attach-enode] #330 0
[assign] #330 justification -1: 
[attach-enode] #331 0
[attach-enode] #310 0
[attach-enode] #332 0
[assign] #332 justification -1: 
[attach-enode] #333 0
[attach-enode] #316 0
[attach-enode] #334 0
[assign] #334 justification -1: 
[attach-enode] #335 0
[attach-enode] #322 0
[attach-enode] #336 0
[assign] #336 justification -1: 
[assign] #1817 justification -1: 
[assign] #1825 justification -1: 
[assign] #1832 justification -1: 
[assign] #1854 justification -1: 
[assign] #1859 justification -1: 
[assign] #1863 justification -1: 
[assign] #1864 justification -1: 
[assign] #463 justification -1: 
[assign] #469 justification -1: 
[assign] #477 justification -1: 
[assign] #485 justification -1: 
[assign] #492 justification -1: 
[assign] #499 justification -1: 
[assign] #505 justification -1: 
[assign] #512 justification -1: 
[assign] #518 justification -1: 
[assign] #523 justification -1: 
[assign] #528 justification -1: 
[assign] #533 justification -1: 
[assign] #538 justification -1: 
[assign] #542 justification -1: 
[assign] #548 justification -1: 
[assign] #563 justification -1: 
[assign] #570 justification -1: 
[assign] #579 justification -1: 
[assign] #588 justification -1: 
[assign] #594 justification -1: 
[assign] #611 justification -1: 
[assign] #618 justification -1: 
[assign] #627 justification -1: 
[assign] #1866 justification -1: 
[assign] #1874 justification -1: 
[assign] #1879 justification -1: 
[assign] #1884 justification -1: 
[assign] #1888 justification -1: 
[assign] #1890 justification -1: 
[assign] #1892 justification -1: 
[assign] #1894 justification -1: 
[assign] #1896 justification -1: 
[assign] #1886 justification -1: 
[assign] #1898 justification -1: 
[assign] #756 justification -1: 
[assign] #1906 justification -1: 
[assign] #1908 justification -1: 
[assign] #1913 justification -1: 
[mk-app] #1948 distinct-aux-f!!2 #792
[mk-app] #1920 unique-value!3
[attach-enode] #1920 0
[mk-app] #1465 = #1948 #1920
[attach-enode] #792 0
[attach-enode] #1948 0
[attach-enode] #1465 0
[assign] #1465 justification -1: 
[mk-app] #1466 distinct-aux-f!!2 #793
[mk-app] #1467 unique-value!4
[attach-enode] #1467 0
[mk-app] #1469 = #1466 #1467
[attach-enode] #793 0
[attach-enode] #1466 0
[attach-enode] #1469 0
[assign] #1469 justification -1: 
[mk-app] #1413 distinct-aux-f!!2 #794
[mk-app] #1414 unique-value!5
[attach-enode] #1414 0
[mk-app] #1415 = #1413 #1414
[attach-enode] #794 0
[attach-enode] #1413 0
[attach-enode] #1415 0
[assign] #1415 justification -1: 
[mk-app] #1417 distinct-aux-f!!2 #795
[mk-app] #1284 unique-value!6
[attach-enode] #1284 0
[mk-app] #1312 = #1417 #1284
[attach-enode] #795 0
[attach-enode] #1417 0
[attach-enode] #1312 0
[assign] #1312 justification -1: 
[mk-app] #1314 distinct-aux-f!!2 #796
[mk-app] #1298 unique-value!7
[attach-enode] #1298 0
[mk-app] #1306 = #1314 #1298
[attach-enode] #796 0
[attach-enode] #1314 0
[attach-enode] #1306 0
[assign] #1306 justification -1: 
[mk-app] #1308 distinct-aux-f!!2 #797
[mk-app] #1299 unique-value!8
[attach-enode] #1299 0
[mk-app] #1300 = #1308 #1299
[attach-enode] #797 0
[attach-enode] #1308 0
[attach-enode] #1300 0
[assign] #1300 justification -1: 
[mk-app] #1302 distinct-aux-f!!2 #798
[mk-app] #1285 unique-value!9
[attach-enode] #1285 0
[mk-app] #1286 = #1302 #1285
[attach-enode] #798 0
[attach-enode] #1302 0
[attach-enode] #1286 0
[assign] #1286 justification -1: 
[mk-app] #1802 distinct-aux-f!!2 #799
[mk-app] #1803 unique-value!10
[attach-enode] #1803 0
[mk-app] #1804 = #1802 #1803
[attach-enode] #799 0
[attach-enode] #1802 0
[attach-enode] #1804 0
[assign] #1804 justification -1: 
[mk-app] #1179 distinct-aux-f!!2 #800
[mk-app] #1176 unique-value!11
[attach-enode] #1176 0
[mk-app] #1177 = #1179 #1176
[attach-enode] #800 0
[attach-enode] #1179 0
[attach-enode] #1177 0
[assign] #1177 justification -1: 
[mk-app] #1180 distinct-aux-f!!2 #801
[mk-app] #1178 unique-value!12
[attach-enode] #1178 0
[mk-app] #1182 = #1180 #1178
[attach-enode] #801 0
[attach-enode] #1180 0
[attach-enode] #1182 0
[assign] #1182 justification -1: 
[mk-app] #1144 distinct-aux-f!!2 #802
[mk-app] #1141 unique-value!13
[attach-enode] #1141 0
[mk-app] #1142 = #1144 #1141
[attach-enode] #802 0
[attach-enode] #1144 0
[attach-enode] #1142 0
[assign] #1142 justification -1: 
[mk-app] #1145 distinct-aux-f!!2 #803
[mk-app] #1143 unique-value!14
[attach-enode] #1143 0
[mk-app] #1147 = #1145 #1143
[attach-enode] #803 0
[attach-enode] #1145 0
[attach-enode] #1147 0
[assign] #1147 justification -1: 
[mk-app] #1121 distinct-aux-f!!2 #804
[mk-app] #1122 unique-value!15
[attach-enode] #1122 0
[mk-app] #1115 = #1121 #1122
[attach-enode] #804 0
[attach-enode] #1121 0
[attach-enode] #1115 0
[assign] #1115 justification -1: 
[mk-app] #1116 distinct-aux-f!!2 #805
[mk-app] #1107 unique-value!16
[attach-enode] #1107 0
[mk-app] #1108 = #1116 #1107
[attach-enode] #805 0
[attach-enode] #1116 0
[attach-enode] #1108 0
[assign] #1108 justification -1: 
[mk-app] #1091 distinct-aux-f!!2 #806
[mk-app] #1092 unique-value!17
[attach-enode] #1092 0
[mk-app] #1084 = #1091 #1092
[attach-enode] #806 0
[attach-enode] #1091 0
[attach-enode] #1084 0
[assign] #1084 justification -1: 
[mk-app] #1085 distinct-aux-f!!2 #807
[mk-app] #1074 unique-value!18
[attach-enode] #1074 0
[mk-app] #1075 = #1085 #1074
[attach-enode] #807 0
[attach-enode] #1085 0
[attach-enode] #1075 0
[assign] #1075 justification -1: 
[mk-app] #1066 distinct-aux-f!!2 #808
[mk-app] #1067 unique-value!19
[attach-enode] #1067 0
[mk-app] #1049 = #1066 #1067
[attach-enode] #808 0
[attach-enode] #1066 0
[attach-enode] #1049 0
[assign] #1049 justification -1: 
[mk-app] #1050 distinct-aux-f!!2 #809
[mk-app] #1041 unique-value!20
[attach-enode] #1041 0
[mk-app] #1042 = #1050 #1041
[attach-enode] #809 0
[attach-enode] #1050 0
[attach-enode] #1042 0
[assign] #1042 justification -1: 
[mk-app] #1033 distinct-aux-f!!2 #810
[mk-app] #1034 unique-value!21
[attach-enode] #1034 0
[mk-app] #973 = #1033 #1034
[attach-enode] #810 0
[attach-enode] #1033 0
[attach-enode] #973 0
[assign] #973 justification -1: 
[mk-app] #974 distinct-aux-f!!2 #811
[mk-app] #975 unique-value!22
[attach-enode] #975 0
[mk-app] #909 = #974 #975
[attach-enode] #811 0
[attach-enode] #974 0
[attach-enode] #909 0
[assign] #909 justification -1: 
[mk-app] #879 distinct-aux-f!!2 #812
[mk-app] #780 unique-value!23
[attach-enode] #780 0
[mk-app] #781 = #879 #780
[attach-enode] #812 0
[attach-enode] #879 0
[attach-enode] #781 0
[assign] #781 justification -1: 
[mk-app] #782 distinct-aux-f!!2 #813
[mk-app] #783 unique-value!24
[attach-enode] #783 0
[mk-app] #744 = #782 #783
[attach-enode] #813 0
[attach-enode] #782 0
[attach-enode] #744 0
[assign] #744 justification -1: 
[mk-app] #745 distinct-aux-f!!2 #814
[mk-app] #746 unique-value!25
[attach-enode] #746 0
[mk-app] #747 = #745 #746
[attach-enode] #814 0
[attach-enode] #745 0
[attach-enode] #747 0
[assign] #747 justification -1: 
[mk-app] #733 distinct-aux-f!!2 #815
[mk-app] #735 unique-value!26
[attach-enode] #735 0
[mk-app] #736 = #733 #735
[attach-enode] #815 0
[attach-enode] #733 0
[attach-enode] #736 0
[assign] #736 justification -1: 
[mk-app] #737 distinct-aux-f!!2 #816
[mk-app] #692 unique-value!27
[attach-enode] #692 0
[mk-app] #723 = #737 #692
[attach-enode] #816 0
[attach-enode] #737 0
[attach-enode] #723 0
[assign] #723 justification -1: 
[mk-app] #724 distinct-aux-f!!2 #817
[mk-app] #681 unique-value!28
[attach-enode] #681 0
[mk-app] #716 = #724 #681
[attach-enode] #817 0
[attach-enode] #724 0
[attach-enode] #716 0
[assign] #716 justification -1: 
[mk-app] #717 distinct-aux-f!!2 #818
[mk-app] #708 unique-value!29
[attach-enode] #708 0
[mk-app] #709 = #717 #708
[attach-enode] #818 0
[attach-enode] #717 0
[attach-enode] #709 0
[assign] #709 justification -1: 
[mk-app] #701 distinct-aux-f!!2 #819
[mk-app] #702 unique-value!30
[attach-enode] #702 0
[mk-app] #693 = #701 #702
[attach-enode] #819 0
[attach-enode] #701 0
[attach-enode] #693 0
[assign] #693 justification -1: 
[mk-app] #694 distinct-aux-f!!2 #820
[mk-app] #682 unique-value!31
[attach-enode] #682 0
[mk-app] #683 = #694 #682
[attach-enode] #820 0
[attach-enode] #694 0
[attach-enode] #683 0
[assign] #683 justification -1: 
[mk-app] #647 distinct-aux-f!!2 #821
[mk-app] #648 unique-value!32
[attach-enode] #648 0
[mk-app] #654 = #647 #648
[attach-enode] #821 0
[attach-enode] #647 0
[attach-enode] #654 0
[assign] #654 justification -1: 
[mk-app] #668 distinct-aux-f!!2 #822
[mk-app] #669 unique-value!33
[attach-enode] #669 0
[mk-app] #670 = #668 #669
[attach-enode] #822 0
[attach-enode] #668 0
[attach-enode] #670 0
[assign] #670 justification -1: 
[mk-app] #671 distinct-aux-f!!2 #823
[mk-app] #653 unique-value!34
[attach-enode] #653 0
[mk-app] #655 = #671 #653
[attach-enode] #823 0
[attach-enode] #671 0
[attach-enode] #655 0
[assign] #655 justification -1: 
[mk-app] #656 distinct-aux-f!!2 #824
[mk-app] #634 unique-value!35
[attach-enode] #634 0
[mk-app] #635 = #656 #634
[attach-enode] #824 0
[attach-enode] #656 0
[attach-enode] #635 0
[assign] #635 justification -1: 
[mk-app] #637 distinct-aux-f!!2 #825
[mk-app] #638 unique-value!36
[attach-enode] #638 0
[mk-app] #435 = #637 #638
[attach-enode] #825 0
[attach-enode] #637 0
[attach-enode] #435 0
[assign] #435 justification -1: 
[mk-app] #436 distinct-aux-f!!2 #826
[mk-app] #437 unique-value!37
[attach-enode] #437 0
[mk-app] #459 = #436 #437
[attach-enode] #826 0
[attach-enode] #436 0
[attach-enode] #459 0
[assign] #459 justification -1: 
[mk-app] #460 distinct-aux-f!!2 #827
[mk-app] #405 unique-value!38
[attach-enode] #405 0
[mk-app] #407 = #460 #405
[attach-enode] #827 0
[attach-enode] #460 0
[attach-enode] #407 0
[assign] #407 justification -1: 
[mk-app] #455 distinct-aux-f!!2 #828
[mk-app] #456 unique-value!39
[attach-enode] #456 0
[mk-app] #374 = #455 #456
[attach-enode] #828 0
[attach-enode] #455 0
[attach-enode] #374 0
[assign] #374 justification -1: 
[mk-app] #376 distinct-aux-f!!2 #829
[mk-app] #449 unique-value!40
[attach-enode] #449 0
[mk-app] #450 = #376 #449
[attach-enode] #829 0
[attach-enode] #376 0
[attach-enode] #450 0
[assign] #450 justification -1: 
[mk-app] #430 distinct-aux-f!!2 #830
[mk-app] #432 unique-value!41
[attach-enode] #432 0
[mk-app] #433 = #430 #432
[attach-enode] #830 0
[attach-enode] #430 0
[attach-enode] #433 0
[assign] #433 justification -1: 
[mk-app] #439 distinct-aux-f!!2 #831
[mk-app] #440 unique-value!42
[attach-enode] #440 0
[mk-app] #441 = #439 #440
[attach-enode] #831 0
[attach-enode] #439 0
[attach-enode] #441 0
[assign] #441 justification -1: 
[mk-app] #442 distinct-aux-f!!2 #832
[mk-app] #398 unique-value!43
[attach-enode] #398 0
[mk-app] #408 = #442 #398
[attach-enode] #832 0
[attach-enode] #442 0
[attach-enode] #408 0
[assign] #408 justification -1: 
[mk-app] #409 distinct-aux-f!!2 #833
[mk-app] #410 unique-value!44
[attach-enode] #410 0
[mk-app] #411 = #409 #410
[attach-enode] #833 0
[attach-enode] #409 0
[attach-enode] #411 0
[assign] #411 justification -1: 
[mk-app] #368 distinct-aux-f!!2 #834
[mk-app] #377 unique-value!45
[attach-enode] #377 0
[mk-app] #378 = #368 #377
[attach-enode] #834 0
[attach-enode] #368 0
[attach-enode] #378 0
[assign] #378 justification -1: 
[mk-app] #379 distinct-aux-f!!2 #835
[mk-app] #380 unique-value!46
[attach-enode] #380 0
[mk-app] #350 = #379 #380
[attach-enode] #835 0
[attach-enode] #379 0
[attach-enode] #350 0
[assign] #350 justification -1: 
[mk-app] #351 distinct-aux-f!!2 #836
[mk-app] #155 unique-value!47
[attach-enode] #155 0
[mk-app] #156 = #351 #155
[attach-enode] #836 0
[attach-enode] #351 0
[attach-enode] #156 0
[assign] #156 justification -1: 
[mk-app] #76 distinct-aux-f!!2 #837
[mk-app] #77 unique-value!48
[attach-enode] #77 0
[mk-app] #78 = #76 #77
[attach-enode] #837 0
[attach-enode] #76 0
[attach-enode] #78 0
[assign] #78 justification -1: 
[mk-app] #2055 distinct-aux-f!!2 #838
[mk-app] #2060 unique-value!49
[attach-enode] #2060 0
[mk-app] #2067 = #2055 #2060
[attach-enode] #838 0
[attach-enode] #2055 0
[attach-enode] #2067 0
[assign] #2067 justification -1: 
[mk-app] #2068 distinct-aux-f!!2 #839
[mk-app] #2069 unique-value!50
[attach-enode] #2069 0
[mk-app] #2070 = #2068 #2069
[attach-enode] #839 0
[attach-enode] #2068 0
[attach-enode] #2070 0
[assign] #2070 justification -1: 
[mk-app] #2071 distinct-aux-f!!2 #840
[mk-app] #2072 unique-value!51
[attach-enode] #2072 0
[mk-app] #2073 = #2071 #2072
[attach-enode] #840 0
[attach-enode] #2071 0
[attach-enode] #2073 0
[assign] #2073 justification -1: 
[mk-app] #2074 distinct-aux-f!!2 #841
[mk-app] #2075 unique-value!52
[attach-enode] #2075 0
[mk-app] #2076 = #2074 #2075
[attach-enode] #841 0
[attach-enode] #2074 0
[attach-enode] #2076 0
[assign] #2076 justification -1: 
[mk-app] #2077 distinct-aux-f!!2 #842
[mk-app] #2078 unique-value!53
[attach-enode] #2078 0
[mk-app] #2079 = #2077 #2078
[attach-enode] #842 0
[attach-enode] #2077 0
[attach-enode] #2079 0
[assign] #2079 justification -1: 
[mk-app] #2080 distinct-aux-f!!2 #843
[mk-app] #2081 unique-value!54
[attach-enode] #2081 0
[mk-app] #2082 = #2080 #2081
[attach-enode] #843 0
[attach-enode] #2080 0
[attach-enode] #2082 0
[assign] #2082 justification -1: 
[mk-app] #2083 distinct-aux-f!!2 #844
[mk-app] #2084 unique-value!55
[attach-enode] #2084 0
[mk-app] #2085 = #2083 #2084
[attach-enode] #844 0
[attach-enode] #2083 0
[attach-enode] #2085 0
[assign] #2085 justification -1: 
[mk-app] #2086 distinct-aux-f!!2 #845
[mk-app] #2087 unique-value!56
[attach-enode] #2087 0
[mk-app] #2088 = #2086 #2087
[attach-enode] #845 0
[attach-enode] #2086 0
[attach-enode] #2088 0
[assign] #2088 justification -1: 
[mk-app] #2089 distinct-aux-f!!2 #846
[mk-app] #2090 unique-value!57
[attach-enode] #2090 0
[mk-app] #2091 = #2089 #2090
[attach-enode] #846 0
[attach-enode] #2089 0
[attach-enode] #2091 0
[assign] #2091 justification -1: 
[mk-app] #2092 distinct-aux-f!!2 #847
[mk-app] #2093 unique-value!58
[attach-enode] #2093 0
[mk-app] #2094 = #2092 #2093
[attach-enode] #847 0
[attach-enode] #2092 0
[attach-enode] #2094 0
[assign] #2094 justification -1: 
[mk-app] #2095 distinct-aux-f!!2 #848
[mk-app] #2096 unique-value!59
[attach-enode] #2096 0
[mk-app] #2097 = #2095 #2096
[attach-enode] #848 0
[attach-enode] #2095 0
[attach-enode] #2097 0
[assign] #2097 justification -1: 
[mk-app] #2098 distinct-aux-f!!2 #849
[mk-app] #2099 unique-value!60
[attach-enode] #2099 0
[mk-app] #2100 = #2098 #2099
[attach-enode] #849 0
[attach-enode] #2098 0
[attach-enode] #2100 0
[assign] #2100 justification -1: 
[mk-app] #2101 distinct-aux-f!!2 #850
[mk-app] #2102 unique-value!61
[attach-enode] #2102 0
[mk-app] #2103 = #2101 #2102
[attach-enode] #850 0
[attach-enode] #2101 0
[attach-enode] #2103 0
[assign] #2103 justification -1: 
[mk-app] #2104 distinct-aux-f!!2 #851
[mk-app] #2105 unique-value!62
[attach-enode] #2105 0
[mk-app] #2106 = #2104 #2105
[attach-enode] #851 0
[attach-enode] #2104 0
[attach-enode] #2106 0
[assign] #2106 justification -1: 
[mk-app] #2107 distinct-aux-f!!2 #852
[mk-app] #2108 unique-value!63
[attach-enode] #2108 0
[mk-app] #2109 = #2107 #2108
[attach-enode] #852 0
[attach-enode] #2107 0
[attach-enode] #2109 0
[assign] #2109 justification -1: 
[mk-app] #2110 distinct-aux-f!!2 #853
[mk-app] #2111 unique-value!64
[attach-enode] #2111 0
[mk-app] #2112 = #2110 #2111
[attach-enode] #853 0
[attach-enode] #2110 0
[attach-enode] #2112 0
[assign] #2112 justification -1: 
[mk-app] #2113 distinct-aux-f!!2 #854
[mk-app] #2114 unique-value!65
[attach-enode] #2114 0
[mk-app] #2115 = #2113 #2114
[attach-enode] #854 0
[attach-enode] #2113 0
[attach-enode] #2115 0
[assign] #2115 justification -1: 
[mk-app] #2116 distinct-aux-f!!2 #855
[mk-app] #2117 unique-value!66
[attach-enode] #2117 0
[mk-app] #2118 = #2116 #2117
[attach-enode] #855 0
[attach-enode] #2116 0
[attach-enode] #2118 0
[assign] #2118 justification -1: 
[mk-app] #2119 distinct-aux-f!!2 #856
[mk-app] #2120 unique-value!67
[attach-enode] #2120 0
[mk-app] #2121 = #2119 #2120
[attach-enode] #856 0
[attach-enode] #2119 0
[attach-enode] #2121 0
[assign] #2121 justification -1: 
[mk-app] #2122 distinct-aux-f!!2 #857
[mk-app] #2123 unique-value!68
[attach-enode] #2123 0
[mk-app] #2124 = #2122 #2123
[attach-enode] #857 0
[attach-enode] #2122 0
[attach-enode] #2124 0
[assign] #2124 justification -1: 
[mk-app] #2125 distinct-aux-f!!2 #858
[mk-app] #2126 unique-value!69
[attach-enode] #2126 0
[mk-app] #2127 = #2125 #2126
[attach-enode] #858 0
[attach-enode] #2125 0
[attach-enode] #2127 0
[assign] #2127 justification -1: 
[mk-app] #2128 distinct-aux-f!!2 #859
[mk-app] #2129 unique-value!70
[attach-enode] #2129 0
[mk-app] #2130 = #2128 #2129
[attach-enode] #859 0
[attach-enode] #2128 0
[attach-enode] #2130 0
[assign] #2130 justification -1: 
[mk-app] #2131 distinct-aux-f!!2 #860
[mk-app] #2132 unique-value!71
[attach-enode] #2132 0
[mk-app] #2133 = #2131 #2132
[attach-enode] #860 0
[attach-enode] #2131 0
[attach-enode] #2133 0
[assign] #2133 justification -1: 
[mk-app] #2134 distinct-aux-f!!2 #861
[mk-app] #2135 unique-value!72
[attach-enode] #2135 0
[mk-app] #2136 = #2134 #2135
[attach-enode] #861 0
[attach-enode] #2134 0
[attach-enode] #2136 0
[assign] #2136 justification -1: 
[mk-app] #2137 distinct-aux-f!!2 #862
[mk-app] #2138 unique-value!73
[attach-enode] #2138 0
[mk-app] #2139 = #2137 #2138
[attach-enode] #862 0
[attach-enode] #2137 0
[attach-enode] #2139 0
[assign] #2139 justification -1: 
[mk-app] #2140 distinct-aux-f!!2 #863
[mk-app] #2141 unique-value!74
[attach-enode] #2141 0
[mk-app] #2142 = #2140 #2141
[attach-enode] #863 0
[attach-enode] #2140 0
[attach-enode] #2142 0
[assign] #2142 justification -1: 
[mk-app] #2143 distinct-aux-f!!2 #864
[mk-app] #2144 unique-value!75
[attach-enode] #2144 0
[mk-app] #2145 = #2143 #2144
[attach-enode] #864 0
[attach-enode] #2143 0
[attach-enode] #2145 0
[assign] #2145 justification -1: 
[mk-app] #2146 distinct-aux-f!!2 #865
[mk-app] #2147 unique-value!76
[attach-enode] #2147 0
[mk-app] #2148 = #2146 #2147
[attach-enode] #865 0
[attach-enode] #2146 0
[attach-enode] #2148 0
[assign] #2148 justification -1: 
[mk-app] #2149 distinct-aux-f!!2 #866
[mk-app] #2150 unique-value!77
[attach-enode] #2150 0
[mk-app] #2151 = #2149 #2150
[attach-enode] #866 0
[attach-enode] #2149 0
[attach-enode] #2151 0
[assign] #2151 justification -1: 
[mk-app] #2152 distinct-aux-f!!2 #867
[mk-app] #2153 unique-value!78
[attach-enode] #2153 0
[mk-app] #2154 = #2152 #2153
[attach-enode] #867 0
[attach-enode] #2152 0
[attach-enode] #2154 0
[assign] #2154 justification -1: 
[mk-app] #2155 distinct-aux-f!!2 #868
[mk-app] #2156 unique-value!79
[attach-enode] #2156 0
[mk-app] #2157 = #2155 #2156
[attach-enode] #868 0
[attach-enode] #2155 0
[attach-enode] #2157 0
[assign] #2157 justification -1: 
[mk-app] #2158 distinct-aux-f!!2 #869
[mk-app] #2159 unique-value!80
[attach-enode] #2159 0
[mk-app] #2160 = #2158 #2159
[attach-enode] #869 0
[attach-enode] #2158 0
[attach-enode] #2160 0
[assign] #2160 justification -1: 
[mk-app] #2161 distinct-aux-f!!2 #870
[mk-app] #2162 unique-value!81
[attach-enode] #2162 0
[mk-app] #2163 = #2161 #2162
[attach-enode] #870 0
[attach-enode] #2161 0
[attach-enode] #2163 0
[assign] #2163 justification -1: 
[mk-app] #2164 distinct-aux-f!!2 #871
[mk-app] #2165 unique-value!82
[attach-enode] #2165 0
[mk-app] #2166 = #2164 #2165
[attach-enode] #871 0
[attach-enode] #2164 0
[attach-enode] #2166 0
[assign] #2166 justification -1: 
[attach-enode] #873 0
[attach-enode] #874 0
[attach-enode] #875 0
[attach-enode] #880 0
[attach-enode] #881 0
[attach-enode] #882 0
[attach-enode] #883 0
[attach-enode] #884 0
[attach-enode] #885 0
[attach-enode] #886 0
[attach-enode] #887 0
[attach-enode] #888 0
[attach-enode] #889 0
[attach-enode] #890 0
[attach-enode] #891 0
[attach-enode] #892 0
[attach-enode] #893 0
[attach-enode] #894 0
[attach-enode] #895 0
[attach-enode] #896 0
[attach-enode] #897 0
[attach-enode] #898 0
[attach-enode] #899 0
[attach-enode] #900 0
[attach-enode] #901 0
[attach-enode] #902 0
[attach-enode] #903 0
[attach-enode] #904 0
[attach-enode] #905 0
[attach-enode] #910 0
[attach-enode] #911 0
[attach-enode] #915 0
[attach-enode] #916 0
[attach-enode] #920 0
[assign] #920 justification -1: 
[attach-enode] #921 0
[assign] #921 justification -1: 
[assign] #915 justification -1: 
[attach-enode] #922 0
[assign] #922 justification -1: 
[attach-enode] #923 0
[assign] #923 justification -1: 
[attach-enode] #924 0
[assign] #924 justification -1: 
[attach-enode] #925 0
[assign] #925 justification -1: 
[attach-enode] #926 0
[assign] #926 justification -1: 
[attach-enode] #927 0
[assign] #927 justification -1: 
[assign] #873 justification -1: 
[assign] #880 justification -1: 
[attach-enode] #928 0
[assign] #928 justification -1: 
[attach-enode] #929 0
[assign] #929 justification -1: 
[attach-enode] #930 0
[assign] #930 justification -1: 
[attach-enode] #931 0
[assign] #931 justification -1: 
[attach-enode] #932 0
[assign] #932 justification -1: 
[assign] #910 justification -1: 
[attach-enode] #933 0
[assign] #933 justification -1: 
[attach-enode] #934 0
[assign] #934 justification -1: 
[attach-enode] #935 0
[assign] #935 justification -1: 
[attach-enode] #936 0
[assign] #936 justification -1: 
[attach-enode] #937 0
[assign] #937 justification -1: 
[attach-enode] #938 0
[assign] #938 justification -1: 
[attach-enode] #939 0
[assign] #939 justification -1: 
[attach-enode] #940 0
[assign] #940 justification -1: 
[attach-enode] #941 0
[assign] #941 justification -1: 
[attach-enode] #942 0
[assign] #942 justification -1: 
[assign] #952 justification -1: 
[assign] #963 justification -1: 
[assign] #1954 justification -1: 
[assign] #980 justification -1: 
[assign] #987 justification -1: 
[assign] #992 justification -1: 
[assign] #999 justification -1: 
[assign] #1005 justification -1: 
[assign] #1016 justification -1: 
[assign] #1019 justification -1: 
[assign] #1959 justification -1: 
[assign] #1963 justification -1: 
[assign] #1967 justification -1: 
[assign] #1974 justification -1: 
[assign] #1976 justification -1: 
[assign] #1979 justification -1: 
[assign] #1981 justification -1: 
[assign] #1986 justification -1: 
[assign] #1988 justification -1: 
[assign] #1990 justification -1: 
[attach-enode] #1123 0
[attach-enode] #1148 0
[attach-enode] #1006 0
[attach-enode] #1183 0
[assign] #1183 justification -1: 
[attach-enode] #1184 0
[assign] #1184 justification -1: 
[assign] #1191 justification -1: 
[assign] #1209 justification -1: 
[attach-enode] #1210 0
[attach-enode] #1224 0
[assign] #1224 justification -1: 
[attach-enode] #1225 0
[attach-enode] #1235 0
[assign] #1235 justification -1: 
[attach-enode] #1236 0
[attach-enode] #1254 0
[assign] #1254 justification -1: 
[attach-enode] #1255 0
[attach-enode] #1267 0
[assign] #1267 justification -1: 
[assign] #1272 justification -1: 
[assign] #2021 justification -1: 
[attach-enode] #1287 0
[assign] #2026 justification -1: 
[assign] #2028 justification -1: 
[attach-enode] #1315 0
[assign] #1315 justification -1: 
[attach-enode] #1316 0
[attach-enode] #1330 0
[assign] #1330 justification -1: 
[assign] #1335 justification -1: 
[assign] #1351 justification -1: 
[attach-enode] #1352 0
[assign] #1371 justification -1: 
[assign] #1377 justification -1: 
[attach-enode] #1378 0
[assign] #1378 justification -1: 
[attach-enode] #1379 0
[attach-enode] #1380 0
[attach-enode] #1381 0
[attach-enode] #1382 0
[attach-enode] #1386 0
[assign] #1386 justification -1: 
[attach-enode] #1387 0
[assign] #1387 justification -1: 
[attach-enode] #1388 0
[attach-enode] #1396 0
[assign] #1396 justification -1: 
[attach-enode] #1397 0
[attach-enode] #1418 0
[assign] #1418 justification -1: 
[attach-enode] #1419 0
[attach-enode] #1434 0
[assign] #1434 justification -1: 
[attach-enode] #1435 0
[attach-enode] #1470 0
[assign] #1470 justification -1: 
[attach-enode] #1471 0
[attach-enode] #1479 0
[assign] #1479 justification -1: 
[attach-enode] #1480 0
[attach-enode] #1488 0
[assign] #1488 justification -1: 
[attach-enode] #1489 0
[attach-enode] #1502 0
[assign] #1502 justification -1: 
[attach-enode] #1503 0
[attach-enode] #1517 0
[assign] #1517 justification -1: 
[attach-enode] #1518 0
[attach-enode] #1526 0
[assign] #1526 justification -1: 
[attach-enode] #1532 0
[attach-enode] #1545 0
[assign] #1545 justification -1: 
[attach-enode] #1546 0
[attach-enode] #1560 0
[assign] #1560 justification -1: 
[attach-enode] #1561 0
[attach-enode] #1573 0
[assign] #1573 justification -1: 
[attach-enode] #1574 0
[assign] #1588 justification -1: 
[attach-enode] #1589 0
[assign] #1589 justification -1: 
[attach-enode] #1590 0
[attach-enode] #1614 0
[assign] #1614 justification -1: 
[attach-enode] #1615 0
[attach-enode] #1642 0
[assign] #1642 justification -1: 
[attach-enode] #1643 0
[assign] #2046 justification -1: 
[assign] #2048 justification -1: 
[assign] #2050 justification -1: 
[assign] #2052 justification -1: 
[assign] #2054 justification -1: 
[assign] #2057 justification -1: 
[assign] #2059 justification -1: 
[assign] #1723 justification -1: 
[assign] #1729 justification -1: 
[assign] #2062 justification -1: 
[assign] #2064 justification -1: 
[assign] #2066 justification -1: 
[assign] #1763 justification -1: 
[assign] #1774 justification -1: 
[assign] #1785 justification -1: 
[assign] #1794 justification -1: 
[assign] #916 bin 211
[assign] #875 bin 180
[assign] #874 bin 180
[assign] #905 bin 183
[assign] #904 bin 183
[assign] #903 bin 183
[assign] #902 bin 183
[assign] #901 bin 183
[assign] #900 bin 183
[assign] #899 bin 183
[assign] #898 bin 183
[assign] #897 bin 183
[assign] #896 bin 183
[assign] #895 bin 183
[assign] #894 bin 183
[assign] #893 bin 183
[assign] #892 bin 183
[assign] #891 bin 183
[assign] #890 bin 183
[assign] #889 bin 183
[assign] #888 bin 183
[assign] #887 bin 183
[assign] #886 bin 183
[assign] #885 bin 183
[assign] #884 bin 183
[assign] #883 bin 183
[assign] #882 bin 183
[assign] #881 bin 183
[assign] #911 bin 209
[attach-enode] #136 0
[attach-enode] #141 0
[attach-enode] #185 0
[attach-enode] #196 0
[attach-enode] #204 0
[attach-enode] #212 0
[attach-enode] #245 0
[attach-enode] #953 0
[eq-expl] #273 root
[eq-expl] #1380 root
[new-match] 0x559938e43208 #1863 #451 #1380 #273 ; #1386
[mk-app] #2167 * #366 #315
[mk-app] #2168 + #1380 #2167
[mk-app] #2169 >= #2168 #337
[mk-app] #2170 not #2169
[mk-app] #2171 * #366 #333
[mk-app] #2172 + #1380 #2171
[mk-app] #2173 >= #2172 #337
[mk-app] #2174 or #2170 #2173
[mk-app] #2175 = #2174 #1386
[mk-app] #2176 not #2175
[mk-app] #2177 + #2167 #1380
[inst-discovered] theory-solving 0 arith# ; #2168
[mk-app] #2178 = #2168 #2177
[instance] 0 #2178
[attach-enode] #2178 0
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #2178 * #366 #1380
[mk-app] #2179 + #315 #2178
[mk-app] #2180 <= #2179 #337
[mk-app] #2181 >= #2177 #337
[inst-discovered] theory-solving 0 arith# ; #2181
[mk-app] #2182 = #2181 #2180
[instance] 0 #2182
[attach-enode] #2182 0
[end-of-instance]
[mk-app] #2177 not #2180
[mk-app] #2181 + #2171 #1380
[inst-discovered] theory-solving 0 arith# ; #2172
[mk-app] #2182 = #2172 #2181
[instance] 0 #2182
[attach-enode] #2182 0
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #2182 + #333 #2178
[mk-app] #2183 <= #2182 #337
[mk-app] #2184 >= #2181 #337
[inst-discovered] theory-solving 0 arith# ; #2184
[mk-app] #2185 = #2184 #2183
[instance] 0 #2185
[attach-enode] #2185 0
[end-of-instance]
[mk-app] #2181 or #2177 #2183
[mk-app] #2184 = #2181 #1386
[mk-app] #2185 not #2181
[mk-app] #2186 not #2184
[inst-discovered] theory-solving 0 basic# ; #2186
[mk-app] #2185 = #2186 #2186
[instance] 0 #2185
[attach-enode] #2185 0
[end-of-instance]
[mk-app] #2185 not #1863
[mk-app] #2187 or #2185 #2186
[instance] 0x559938e43208 ; 1
[attach-enode] #366 1
[attach-enode] #2178 1
[attach-enode] #2179 1
[attach-enode] #2182 1
[assign] (not #2184) justification -1: 60
[end-of-instance]
[assign] (not #2181) bin -364
[assign] (not #2183) bin -363
[assign] #2180 bin -363
[mk-app] #2188 <= #315 #319
[mk-app] #2189 >= #315 #319
[assign] #2188 justification -1: 48
[assign] #2189 justification -1: 48
[mk-app] #2190 = #316 #333
[mk-app] #2191 <= #333 #316
[mk-app] #2192 >= #333 #316
[assign] #2190 justification -1: 53
[attach-enode] #2190 0
[assign] #2191 justification -1: 367
[assign] #2192 justification -1: 367
[push] 0
[mk-app] #2193 a!
[mk-app] #2194 <= #337 #2193
[attach-meaning] #366 arith (- 1)
[mk-app] #2195 * #366 #2193
[mk-app] #2196 >= #2193 #337
[inst-discovered] theory-solving 0 arith# ; #2194
[mk-app] #2195 = #2194 #2196
[instance] 0 #2195
[attach-enode] #2195 0
[end-of-instance]
[mk-app] #2195 b!
[mk-app] #2197 <= #337 #2195
[attach-meaning] #366 arith (- 1)
[mk-app] #2198 * #366 #2195
[mk-app] #2199 >= #2195 #337
[inst-discovered] theory-solving 0 arith# ; #2197
[mk-app] #2198 = #2197 #2199
[instance] 0 #2198
[attach-enode] #2198 0
[end-of-instance]
[mk-app] #2198 %%location_label%%0
[mk-app] #2200 I #2193
[mk-app] #2201 the_q!model.pow2.? #2200
[mk-app] #2202 Sub #2195 #292
[mk-app] #2203 nClip #2202
[mk-app] #2204 I #2203
[mk-app] #2205 the_q!model.pow2.? #2204
[mk-app] #2206 Mul #2201 #2205
[mk-app] #2207 Mul #1196 #2206
[mk-app] #2208 Mul #1196 #2205
[mk-app] #2209 Mul #2201 #2208
[mk-app] #2210 = #2207 #2209
[mk-app] #2211 => #2198 #2210
[mk-app] #2212 not #2211
[mk-app] #2213 not #2198
[mk-app] #2214 or #2213 #2210
[inst-discovered] theory-solving 0 basic# ; #2211
[mk-app] #2215 = #2211 #2214
[instance] 0 #2215
[attach-enode] #2215 0
[end-of-instance]
[mk-app] #2215 not #2214
[mk-app] #2216 not #2210
[begin-check] 1
[assign] #23 justification -1: 
[attach-enode] #2193 0
[assign] #2196 justification -1: 
[attach-enode] #2195 0
[assign] #2199 justification -1: 
[assign] #2198 justification -1: 
[attach-enode] #1196 0
[attach-enode] #2200 0
[attach-enode] #2201 0
[attach-enode] #2202 0
[attach-enode] #2203 0
[attach-enode] #2204 0
[attach-enode] #2205 0
[attach-enode] #2206 0
[attach-enode] #2207 0
[attach-enode] #2208 0
[attach-enode] #2209 0
[attach-enode] #2210 0
[assign] (not #2210) justification -1: 
[assign] #29 bin 1
[eq-expl] #2201 root
[eq-expl] #2208 root
[new-match] 0x559938e44030 #570 #564 #2208 #2201 ; #2209
[new-match] 0x559938e44068 #1866 #564 #2208 #2201 ; #2209
[eq-expl] #1196 root
[eq-expl] #2206 root
[new-match] 0x559938e440a0 #570 #564 #2206 #1196 ; #2207
[new-match] 0x559938e440d8 #1866 #564 #2206 #1196 ; #2207
[eq-expl] #2205 root
[new-match] 0x559938e44110 #570 #564 #2205 #1196 ; #2208
[new-match] 0x559938e44148 #1866 #564 #2205 #1196 ; #2208
[new-match] 0x559938e44180 #570 #564 #2205 #2201 ; #2206
[new-match] 0x559938e441b8 #1866 #564 #2205 #2201 ; #2206
[eq-expl] #2193 root
[new-match] 0x559938e441f0 #170 #169 #2193 ; #2200
[eq-expl] #2203 root
[new-match] 0x559938e44220 #170 #169 #2203 ; #2204
[eq-expl] #2202 root
[new-match] 0x559938e44250 #1817 #344 #2202 ; #2203
[eq-expl] #2195 root
[eq-expl] #292 root
[new-match] 0x559938e44280 #563 #555 #292 #2195 ; #2202
[mk-app] #2174 * #2208 #2201
[mk-app] #2175 * #366 #2174
[mk-app] #2176 + #2209 #2175
[mk-app] #2213 = #2176 #337
[mk-app] #2214 * #2201 #2208
[inst-discovered] theory-solving 0 arith# ; #2174
[mk-app] #2215 = #2174 #2214
[instance] 0 #2215
[attach-enode] #2215 0
[end-of-instance]
[mk-app] #2215 * #366 #2214
[mk-app] #2217 + #2209 #2215
[mk-app] #2218 = #2217 #337
[mk-app] #2219 not #570
[mk-app] #2220 or #2219 #2218
[instance] 0x559938e44030 ; 1
[attach-enode] #2214 1
[attach-enode] #2215 1
[attach-enode] #2217 1
[attach-enode] #2218 1
[mk-app] #2221 = #337 #2217
[mk-app] #2222 <= #2217 #337
[mk-app] #2223 >= #2217 #337
[attach-enode] #2221 1
[assign] #2218 justification -1: 78
[end-of-instance]
[mk-app] #2224 >= #2201 #337
[mk-app] #2225 not #2224
[mk-app] #2226 >= #2208 #337
[mk-app] #2227 not #2226
[mk-app] #2228 >= #2209 #337
[mk-app] #2229 or #2225 #2227 #2228
[mk-app] #2230 not #1866
[mk-app] #2231 or #2230 #2225 #2227 #2228
[instance] 0x559938e44068 ; 1
[end-of-instance]
[mk-app] #2232 * #2206 #1196
[mk-app] #2233 * #366 #2232
[mk-app] #2234 + #2207 #2233
[mk-app] #2235 = #2234 #337
[mk-app] #2236 * #1196 #2206
[inst-discovered] theory-solving 0 arith# ; #2232
[mk-app] #2237 = #2232 #2236
[instance] 0 #2237
[attach-enode] #2237 0
[end-of-instance]
[mk-app] #2237 Int
[attach-meaning] #2237 arith (- 2)
[mk-app] #2238 * #2237 #2206
[mk-app] #2239 * #366 #2236
[inst-discovered] theory-solving 0 arith# ; #2239
[mk-app] #2240 = #2239 #2238
[instance] 0 #2240
[attach-enode] #2240 0
[end-of-instance]
[mk-app] #2236 + #2238 #2207
[mk-app] #2239 + #2207 #2238
[inst-discovered] theory-solving 0 arith# ; #2239
[mk-app] #2240 = #2239 #2236
[instance] 0 #2240
[attach-enode] #2240 0
[end-of-instance]
[mk-app] #2239 * #1196 #2206
[attach-meaning] #366 arith (- 1)
[mk-app] #2240 * #366 #2207
[mk-app] #2241 + #2239 #2240
[mk-app] #2242 = #2241 #337
[mk-app] #2243 = #2236 #337
[inst-discovered] theory-solving 0 arith# ; #2243
[mk-app] #2244 = #2243 #2242
[instance] 0 #2244
[attach-enode] #2244 0
[end-of-instance]
[mk-app] #2237 or #2219 #2242
[instance] 0x559938e440a0 ; 1
[attach-enode] #2239 1
[attach-enode] #2240 1
[attach-enode] #2241 1
[attach-enode] #2242 1
[mk-app] #2238 = #337 #2241
[mk-app] #2236 <= #2241 #337
[mk-app] #2243 >= #2241 #337
[attach-enode] #2238 1
[assign] #2242 justification -1: 78
[end-of-instance]
[mk-app] #2244 >= #1196 #337
[mk-app] #2245 not #2244
[mk-app] #2246 >= #2206 #337
[mk-app] #2247 not #2246
[mk-app] #2248 >= #2207 #337
[mk-app] #2249 or #2245 #2247 #2248
[mk-app] #2250 Int
[attach-meaning] #2250 arith (- 2)
[inst-discovered] theory-solving 0 arith# ; #2244
[mk-app] #2250 = #2244 #1
[instance] 0 #2250
[attach-enode] #2250 0
[end-of-instance]
[mk-app] #2250 not #1
[inst-discovered] theory-solving 0 basic# ; #2250
[mk-app] #2251 = #2250 #2
[instance] 0 #2251
[attach-enode] #2251 0
[end-of-instance]
[mk-app] #2250 or #2247 #2248
[mk-app] #2251 or #2 #2247 #2248
[inst-discovered] theory-solving 0 basic# ; #2251
[mk-app] #2252 = #2251 #2250
[instance] 0 #2252
[attach-enode] #2252 0
[end-of-instance]
[mk-app] #2251 or #2230 #2247 #2248
[instance] 0x559938e440d8 ; 1
[end-of-instance]
[mk-app] #2250 * #2205 #1196
[mk-app] #2252 * #366 #2250
[mk-app] #2253 + #2208 #2252
[mk-app] #2254 = #2253 #337
[mk-app] #2255 * #1196 #2205
[inst-discovered] theory-solving 0 arith# ; #2250
[mk-app] #2256 = #2250 #2255
[instance] 0 #2256
[attach-enode] #2256 0
[end-of-instance]
[mk-app] #2256 Int
[attach-meaning] #2256 arith (- 2)
[mk-app] #2257 * #2256 #2205
[mk-app] #2258 * #366 #2255
[inst-discovered] theory-solving 0 arith# ; #2258
[mk-app] #2259 = #2258 #2257
[instance] 0 #2259
[attach-enode] #2259 0
[end-of-instance]
[mk-app] #2255 + #2257 #2208
[mk-app] #2258 + #2208 #2257
[inst-discovered] theory-solving 0 arith# ; #2258
[mk-app] #2259 = #2258 #2255
[instance] 0 #2259
[attach-enode] #2259 0
[end-of-instance]
[mk-app] #2258 * #1196 #2205
[attach-meaning] #366 arith (- 1)
[mk-app] #2259 * #366 #2208
[mk-app] #2260 + #2258 #2259
[mk-app] #2261 = #2260 #337
[mk-app] #2262 = #2255 #337
[inst-discovered] theory-solving 0 arith# ; #2262
[mk-app] #2263 = #2262 #2261
[instance] 0 #2263
[attach-enode] #2263 0
[end-of-instance]
[mk-app] #2256 or #2219 #2261
[instance] 0x559938e44110 ; 1
[attach-enode] #2258 1
[attach-enode] #2259 1
[attach-enode] #2260 1
[attach-enode] #2261 1
[mk-app] #2257 = #337 #2260
[mk-app] #2255 <= #2260 #337
[mk-app] #2262 >= #2260 #337
[attach-enode] #2257 1
[assign] #2261 justification -1: 78
[end-of-instance]
[mk-app] #2263 >= #2205 #337
[mk-app] #2264 not #2263
[mk-app] #2265 or #2245 #2264 #2226
[mk-app] #2266 or #2264 #2226
[mk-app] #2267 or #2 #2264 #2226
[inst-discovered] theory-solving 0 basic# ; #2267
[mk-app] #2268 = #2267 #2266
[instance] 0 #2268
[attach-enode] #2268 0
[end-of-instance]
[mk-app] #2267 or #2230 #2264 #2226
[instance] 0x559938e44148 ; 1
[end-of-instance]
[mk-app] #2266 * #2205 #2201
[mk-app] #2268 * #366 #2266
[mk-app] #2269 + #2206 #2268
[mk-app] #2270 = #2269 #337
[mk-app] #2271 * #2201 #2205
[inst-discovered] theory-solving 0 arith# ; #2266
[mk-app] #2272 = #2266 #2271
[instance] 0 #2272
[attach-enode] #2272 0
[end-of-instance]
[mk-app] #2272 * #366 #2271
[mk-app] #2273 + #2206 #2272
[mk-app] #2274 = #2273 #337
[mk-app] #2275 or #2219 #2274
[instance] 0x559938e44180 ; 1
[attach-enode] #2271 1
[attach-enode] #2272 1
[attach-enode] #2273 1
[attach-enode] #2274 1
[mk-app] #2276 = #337 #2273
[mk-app] #2277 <= #2273 #337
[mk-app] #2278 >= #2273 #337
[attach-enode] #2276 1
[assign] #2274 justification -1: 78
[end-of-instance]
[mk-app] #2279 or #2225 #2264 #2246
[mk-app] #2280 or #2230 #2225 #2264 #2246
[instance] 0x559938e441b8 ; 1
[end-of-instance]
[mk-app] #2281 %I #2200
[mk-app] #2282 = #2193 #2281
[mk-app] #2283 not #170
[mk-app] #2284 or #2283 #2282
[instance] 0x559938e441f0 ; 1
[attach-enode] #2281 1
[attach-enode] #2282 1
[assign] #2282 justification -1: 25
[end-of-instance]
[mk-app] #2285 %I #2204
[mk-app] #2286 = #2203 #2285
[mk-app] #2287 or #2283 #2286
[instance] 0x559938e44220 ; 1
[attach-enode] #2285 1
[attach-enode] #2286 1
[assign] #2286 justification -1: 25
[end-of-instance]
[mk-app] #2288 >= #2203 #337
[mk-app] #2289 not #2288
[mk-app] #2290 >= #2202 #337
[mk-app] #2291 not #2290
[mk-app] #2292 = #2202 #2203
[mk-app] #2293 or #2291 #2292
[mk-app] #2294 not #2293
[mk-app] #2295 or #2289 #2294
[mk-app] #2296 not #2295
[mk-app] #2297 not #1817
[mk-app] #2298 or #2297 #2296
[instance] 0x559938e44250 ; 1
[attach-enode] #2292 1
[attach-meaning] #366 arith (- 1)
[mk-app] #2299 * #366 #2203
[mk-app] #2300 + #2202 #2299
[mk-app] #2301 <= #2300 #337
[mk-app] #2302 >= #2300 #337
[attach-enode] #2299 1
[attach-enode] #2300 1
[assign] (not #2295) justification -1: 55
[end-of-instance]
[mk-app] #2303 * #366 #2195
[mk-app] #2304 + #292 #2303 #2202
[mk-app] #2305 = #2304 #337
[attach-meaning] #366 arith (- 1)
[mk-app] #2306 + #2303 #2202
[attach-meaning] #366 arith (- 1)
[mk-app] #2307 * #366 #2202
[mk-app] #2308 + #2195 #2307
[mk-app] #2306 = #2308 #292
[inst-discovered] theory-solving 0 arith# ; #2305
[mk-app] #2309 = #2305 #2306
[instance] 0 #2309
[attach-enode] #2309 0
[end-of-instance]
[mk-app] #2309 not #563
[mk-app] #2310 or #2309 #2306
[instance] 0x559938e44280 ; 1
[attach-enode] #2307 1
[attach-enode] #2308 1
[attach-enode] #2306 1
[mk-app] #2311 = #292 #2308
[mk-app] #2312 <= #2308 #292
[mk-app] #2313 >= #2308 #292
[attach-enode] #2311 1
[assign] #2306 justification -1: 77
[end-of-instance]
[assign] #2288 clause 398 404
[assign] #2293 clause 403 404
[assign] #2221 justification -1: 374
[assign] #2238 justification -1: 381
[assign] #2257 justification -1: 387
[assign] #2276 justification -1: 392
[assign] #2311 justification -1: 405
[attach-meaning] #366 arith (- 1)
[mk-app] #2314 * #366 #2209
[mk-app] #2315 + #2207 #2314
[mk-app] #2316 <= #2315 #337
[mk-app] #2317 >= #2315 #337
[attach-enode] #2314 0
[attach-enode] #2315 0
[assign] #2222 clause 376 -375
[assign] #2223 clause 377 -375
[assign] #2236 clause 383 -382
[assign] #2243 clause 384 -382
[assign] #2255 clause 389 -388
[assign] #2262 clause 390 -388
[assign] #2277 clause 394 -393
[assign] #2278 clause 395 -393
[assign] #2312 clause 407 -406
[assign] #2313 clause 408 -406
[decide-and-or] #275 #272
[push] 1
[assign] #272 decision axiom
[decide-and-or] #1991 #1146
[push] 2
[assign] (not #1123) decision axiom
[eq-expl] #792 root
[new-match] 0x559938e70600 #29 #28 #792 ; #1123
[mk-app] #2318 = #1123 #874
[mk-app] #2319 not #29
[mk-app] #2320 or #2319 #2318
[instance] 0x559938e70600 ; 1
[assign] (not #2318) justification -1: 181 -256
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2318
[conflict] #2318
[pop] 1 3
[assign] #2318 axiom
[assign] #1123 clause 256 -411
[assign] #1995 bin 256
[decide-and-or] #1999 #1181
[push] 2
[assign] (not #1148) decision axiom
[eq-expl] #793 root
[new-match] 0x559938e70660 #29 #28 #793 ; #1148
[mk-app] #2319 = #1148 #875
[mk-app] #2320 not #29
[mk-app] #2321 or #2320 #2319
[instance] 0x559938e70660 ; 1
[assign] (not #2319) justification -1: 182 -258
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2319
[conflict] #2319
[pop] 1 3
[assign] #2319 axiom
[assign] #1148 clause 258 -412
[assign] #2006 bin 258
[decide-and-or] #1223 #1222
[push] 2
[assign] (not #1210) decision axiom
[eq-expl] #794 root
[new-match] 0x559938e706c0 #29 #28 #794 ; #1210
[mk-app] #2320 = #1210 #1184
[mk-app] #2321 not #29
[mk-app] #2322 or #2321 #2320
[instance] 0x559938e706c0 ; 1
[assign] (not #2320) justification -1: 261 -264
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2320
[conflict] #2320
[pop] 1 3
[assign] #2320 axiom
[assign] #1210 clause 264 -413
[assign] #1221 bin 264
[eq-expl] #2200 root
[new-match] 0x559938e70708 #1221 #1217 #2200 ; #2201
[eq-expl] #2204 root
[new-match] 0x559938e70738 #1221 #1217 #2204 ; #2205
[mk-app] #2321 has_type #2200 #196
[mk-app] #2322 not #2321
[mk-app] #2323 the_q!model.rec%pow2.? #2200 #1213
[mk-app] #2324 = #2201 #2323
[mk-app] #2325 or #2322 #2324
[mk-app] #2326 not #1221
[mk-app] #2327 or #2326 #2322 #2324
[instance] 0x559938e70708 ; 1
[attach-enode] #2321 1
[attach-enode] #1212 1
[attach-enode] #1213 1
[attach-enode] #2323 1
[attach-enode] #2324 1
[end-of-instance]
[mk-app] #2328 has_type #2204 #196
[mk-app] #2329 not #2328
[mk-app] #2330 the_q!model.rec%pow2.? #2204 #1213
[mk-app] #2331 = #2205 #2330
[mk-app] #2332 or #2329 #2331
[mk-app] #2333 or #2326 #2329 #2331
[instance] 0x559938e70738 ; 1
[attach-enode] #2328 1
[attach-enode] #2330 1
[attach-enode] #2331 1
[end-of-instance]
[decide-and-or] #1234 #1233
[push] 2
[assign] (not #1225) decision axiom
[eq-expl] #795 root
[new-match] 0x559938e70c28 #29 #28 #795 ; #1225
[mk-app] #2334 = #1225 #1224
[mk-app] #2335 not #29
[mk-app] #2336 or #2335 #2334
[instance] 0x559938e70c28 ; 1
[assign] (not #2334) justification -1: 266 -267
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2334
[conflict] #2334
[pop] 1 3
[assign] #2334 axiom
[assign] #1225 clause 267 -418
[assign] #1231 bin 267
[decide-and-or] #1253 #1252
[push] 2
[assign] (not #1236) decision axiom
[eq-expl] #796 root
[new-match] 0x559938e70c88 #29 #28 #796 ; #1236
[mk-app] #2335 = #1236 #1235
[mk-app] #2336 not #29
[mk-app] #2337 or #2336 #2335
[instance] 0x559938e70c88 ; 1
[assign] (not #2335) justification -1: 269 -270
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2335
[conflict] #2335
[pop] 1 3
[assign] #2335 axiom
[assign] #1236 clause 270 -419
[assign] #1251 bin 270
[decide-and-or] #2016 #1265
[push] 2
[assign] (not #1255) decision axiom
[eq-expl] #797 root
[new-match] 0x559938e70ce8 #29 #28 #797 ; #1255
[mk-app] #2336 = #1255 #1254
[mk-app] #2337 not #29
[mk-app] #2338 or #2337 #2336
[instance] 0x559938e70ce8 ; 1
[assign] (not #2336) justification -1: 272 -273
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2336
[conflict] #2336
[pop] 1 3
[assign] #2336 axiom
[assign] #1255 clause 273 -420
[assign] #2015 bin 273
[decide-and-or] #2018 #1301
[push] 2
[assign] (not #1287) decision axiom
[eq-expl] #798 root
[new-match] 0x559938e70d48 #29 #28 #798 ; #1287
[mk-app] #2337 = #1287 #1267
[mk-app] #2338 not #29
[mk-app] #2339 or #2338 #2337
[instance] 0x559938e70d48 ; 1
[assign] (not #2337) justification -1: 275 -278
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2337
[conflict] #2337
[pop] 1 3
[assign] #2337 axiom
[assign] #1287 clause 278 -421
[assign] #2023 bin 278
[decide-and-or] #1329 #1328
[push] 2
[assign] (not #1316) decision axiom
[eq-expl] #799 root
[new-match] 0x559938e70da8 #29 #28 #799 ; #1316
[mk-app] #2338 = #1316 #1315
[mk-app] #2339 not #29
[mk-app] #2340 or #2339 #2338
[instance] 0x559938e70da8 ; 1
[assign] (not #2338) justification -1: 282 -283
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2338
[conflict] #2338
[pop] 1 3
[assign] #2338 axiom
[assign] #1316 clause 283 -422
[assign] #1326 bin 283
[decide-and-or] #1365 #1364
[push] 2
[assign] (not #1352) decision axiom
[eq-expl] #800 root
[new-match] 0x559938e70e08 #29 #28 #800 ; #1352
[mk-app] #2339 = #1352 #1330
[mk-app] #2340 not #29
[mk-app] #2341 or #2340 #2339
[instance] 0x559938e70e08 ; 1
[assign] (not #2339) justification -1: 285 -288
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2339
[conflict] #2339
[pop] 1 3
[assign] #2339 axiom
[assign] #1352 clause 288 -423
[assign] #1363 bin 288
[decide-and-or] #1385 #1384
[push] 2
[assign] (not #1379) decision axiom
[eq-expl] #817 root
[new-match] 0x559938e70e68 #29 #28 #817 ; #1379
[mk-app] #2340 = #1379 #1378
[mk-app] #2341 not #29
[mk-app] #2342 or #2341 #2340
[instance] 0x559938e70e68 ; 1
[assign] (not #2340) justification -1: 292 -293
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2340
[conflict] #2340
[pop] 1 3
[assign] #2340 axiom
[assign] #1379 clause 293 -424
[assign] #1382 bin 293
[mk-app] #2341 <= #1380 #1381
[mk-app] #2342 >= #1380 #1381
[assign] #2341 justification -1: 294
[assign] #2342 justification -1: 294
[decide-and-or] #1395 #1394
[push] 2
[assign] (not #1388) decision axiom
[eq-expl] #801 root
[new-match] 0x559938e70fd0 #29 #28 #801 ; #1388
[mk-app] #2343 = #1388 #1387
[mk-app] #2344 not #29
[mk-app] #2345 or #2344 #2343
[instance] 0x559938e70fd0 ; 1
[assign] (not #2343) justification -1: 296 -297
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2343
[conflict] #2343
[pop] 1 3
[assign] #2343 axiom
[assign] #1388 clause 297 -427
[assign] #1392 bin 297
[decide-and-or] #2033 #1416
[push] 2
[assign] (not #1397) decision axiom
[eq-expl] #802 root
[new-match] 0x559938e71030 #29 #28 #802 ; #1397
[mk-app] #2344 = #1397 #1396
[mk-app] #2345 not #29
[mk-app] #2346 or #2345 #2344
[instance] 0x559938e71030 ; 1
[assign] (not #2344) justification -1: 299 -300
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2344
[conflict] #2344
[pop] 1 3
[assign] #2344 axiom
[assign] #1397 clause 300 -428
[assign] #2030 bin 300
[decide-and-or] #1433 #1432
[push] 2
[assign] (not #1419) decision axiom
[eq-expl] #803 root
[new-match] 0x559938e71090 #29 #28 #803 ; #1419
[mk-app] #2345 = #1419 #1418
[mk-app] #2346 not #29
[mk-app] #2347 or #2346 #2345
[instance] 0x559938e71090 ; 1
[assign] (not #2345) justification -1: 302 -303
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2345
[conflict] #2345
[pop] 1 3
[assign] #2345 axiom
[assign] #1419 clause 303 -429
[assign] #1431 bin 303
[decide-and-or] #2042 #1468
[push] 2
[assign] (not #1435) decision axiom
[eq-expl] #804 root
[new-match] 0x559938e710f0 #29 #28 #804 ; #1435
[mk-app] #2346 = #1435 #1434
[mk-app] #2347 not #29
[mk-app] #2348 or #2347 #2346
[instance] 0x559938e710f0 ; 1
[assign] (not #2346) justification -1: 305 -306
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2346
[conflict] #2346
[pop] 1 3
[assign] #2346 axiom
[assign] #1435 clause 306 -430
[assign] #2039 bin 306
[decide-and-or] #1478 #1477
[push] 2
[assign] (not #1471) decision axiom
[eq-expl] #805 root
[new-match] 0x559938e71150 #29 #28 #805 ; #1471
[mk-app] #2347 = #1471 #1470
[mk-app] #2348 not #29
[mk-app] #2349 or #2348 #2347
[instance] 0x559938e71150 ; 1
[assign] (not #2347) justification -1: 308 -309
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2347
[conflict] #2347
[pop] 1 3
[assign] #2347 axiom
[assign] #1471 clause 309 -431
[assign] #1475 bin 309
[decide-and-or] #1487 #1486
[push] 2
[assign] (not #1480) decision axiom
[eq-expl] #806 root
[new-match] 0x559938e711b0 #29 #28 #806 ; #1480
[mk-app] #2348 = #1480 #1479
[mk-app] #2349 not #29
[mk-app] #2350 or #2349 #2348
[instance] 0x559938e711b0 ; 1
[assign] (not #2348) justification -1: 311 -312
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2348
[conflict] #2348
[pop] 1 3
[assign] #2348 axiom
[assign] #1480 clause 312 -432
[assign] #1484 bin 312
[decide-and-or] #1501 #1500
[push] 2
[assign] (not #1489) decision axiom
[eq-expl] #807 root
[new-match] 0x559938e71210 #29 #28 #807 ; #1489
[mk-app] #2349 = #1489 #1488
[mk-app] #2350 not #29
[mk-app] #2351 or #2350 #2349
[instance] 0x559938e71210 ; 1
[assign] (not #2349) justification -1: 314 -315
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2349
[conflict] #2349
[pop] 1 3
[assign] #2349 axiom
[assign] #1489 clause 315 -433
[assign] #1498 bin 315
[decide-and-or] #1516 #1515
[push] 2
[assign] (not #1503) decision axiom
[eq-expl] #808 root
[new-match] 0x559938e71270 #29 #28 #808 ; #1503
[mk-app] #2350 = #1503 #1502
[mk-app] #2351 not #29
[mk-app] #2352 or #2351 #2350
[instance] 0x559938e71270 ; 1
[assign] (not #2350) justification -1: 317 -318
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2350
[conflict] #2350
[pop] 1 3
[assign] #2350 axiom
[assign] #1503 clause 318 -434
[assign] #1514 bin 318
[decide-and-or] #1525 #1528
[push] 2
[assign] (not #1518) decision axiom
[eq-expl] #809 root
[new-match] 0x559938e712d0 #29 #28 #809 ; #1518
[mk-app] #2351 = #1518 #1517
[mk-app] #2352 not #29
[mk-app] #2353 or #2352 #2351
[instance] 0x559938e712d0 ; 1
[assign] (not #2351) justification -1: 320 -321
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2351
[conflict] #2351
[pop] 1 3
[assign] #2351 axiom
[assign] #1518 clause 321 -435
[assign] #1531 bin 321
[decide-and-or] #1544 #1543
[push] 2
[assign] (not #1532) decision axiom
[eq-expl] #810 root
[new-match] 0x559938e71330 #29 #28 #810 ; #1532
[mk-app] #2352 = #1532 #1526
[mk-app] #2353 not #29
[mk-app] #2354 or #2353 #2352
[instance] 0x559938e71330 ; 1
[assign] (not #2352) justification -1: 323 -324
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2352
[conflict] #2352
[pop] 1 3
[assign] #2352 axiom
[assign] #1532 clause 324 -436
[assign] #1541 bin 324
[decide-and-or] #1559 #1558
[push] 2
[assign] (not #1546) decision axiom
[eq-expl] #811 root
[new-match] 0x559938e71390 #29 #28 #811 ; #1546
[mk-app] #2353 = #1546 #1545
[mk-app] #2354 not #29
[mk-app] #2355 or #2354 #2353
[instance] 0x559938e71390 ; 1
[assign] (not #2353) justification -1: 326 -327
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2353
[conflict] #2353
[pop] 1 3
[assign] #2353 axiom
[assign] #1546 clause 327 -437
[assign] #1557 bin 327
[decide-and-or] #1572 #1571
[push] 2
[assign] (not #1561) decision axiom
[eq-expl] #812 root
[new-match] 0x559938e713f0 #29 #28 #812 ; #1561
[mk-app] #2354 = #1561 #1560
[mk-app] #2355 not #29
[mk-app] #2356 or #2355 #2354
[instance] 0x559938e713f0 ; 1
[assign] (not #2354) justification -1: 329 -330
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2354
[conflict] #2354
[pop] 1 3
[assign] #2354 axiom
[assign] #1561 clause 330 -438
[assign] #1570 bin 330
[decide-and-or] #1582 #1581
[push] 2
[assign] (not #1574) decision axiom
[eq-expl] #813 root
[new-match] 0x559938e71450 #29 #28 #813 ; #1574
[mk-app] #2355 = #1574 #1573
[mk-app] #2356 not #29
[mk-app] #2357 or #2356 #2355
[instance] 0x559938e71450 ; 1
[assign] (not #2355) justification -1: 332 -333
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2355
[conflict] #2355
[pop] 1 3
[assign] #2355 axiom
[assign] #1574 clause 333 -439
[assign] #1579 bin 333
[decide-and-or] #1613 #1612
[push] 2
[assign] (not #1590) decision axiom
[eq-expl] #814 root
[new-match] 0x559938e7c698 #29 #28 #814 ; #1590
[mk-app] #2356 = #1590 #1589
[mk-app] #2357 not #29
[mk-app] #2358 or #2357 #2356
[instance] 0x559938e7c698 ; 1
[assign] (not #2356) justification -1: 336 -337
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2356
[conflict] #2356
[pop] 1 3
[assign] #2356 axiom
[assign] #1590 clause 337 -440
[assign] #1611 bin 337
[decide-and-or] #1641 #1640
[push] 2
[assign] (not #1615) decision axiom
[eq-expl] #815 root
[new-match] 0x559938e7c6d8 #29 #28 #815 ; #1615
[mk-app] #2357 = #1615 #1614
[mk-app] #2358 not #29
[mk-app] #2359 or #2358 #2357
[instance] 0x559938e7c6d8 ; 1
[assign] (not #2357) justification -1: 339 -340
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2357
[conflict] #2357
[pop] 1 3
[assign] #2357 axiom
[assign] #1615 clause 340 -441
[assign] #1639 bin 340
[decide-and-or] #1669 #1668
[push] 2
[assign] (not #1643) decision axiom
[eq-expl] #816 root
[new-match] 0x559938e7c738 #29 #28 #816 ; #1643
[mk-app] #2358 = #1643 #1642
[mk-app] #2359 not #29
[mk-app] #2360 or #2359 #2358
[instance] 0x559938e7c738 ; 1
[assign] (not #2358) justification -1: 342 -343
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2358
[conflict] #2358
[pop] 1 3
[assign] #2358 axiom
[assign] #1643 clause 343 -442
[assign] #1667 bin 343
[decide-and-or] #2231 #2225
[push] 2
[assign] (not #2224) decision axiom
[decide-and-or] #2251 #2247
[push] 3
[assign] (not #2246) decision axiom
[assign] (not #2248) clause -386 385 -384
[decide-and-or] #2267 #2264
[push] 4
[assign] (not #2263) decision axiom
[assign] (not #2226) clause -379 391 -390
[push] 5
[assign] (not #2292) decision axiom
[assign] (not #2290) clause -399 400
[assign] #2301 clause 401 399 -398
[assign] (not #2302) clause -402 399 -398
[push] 6
[assign] (not #2316) decision axiom
[assign] #2317 clause 410 409
[assign] (not #2228) clause -380 409 385 -384
[decide-and-or] #2327 #2322
[push] 7
[assign] (not #2321) decision axiom
[eq-expl] #196 root
[new-match] 0x559938e7c8e8 #518 #199 #2200 ; #2321 (#196 #196)
[new-match] 0x559938e7c918 #203 #199 #2200 ; #2321 (#196 #196)
[eq-expl] #2193 lit #2282 ; #2281
[eq-expl] #2281 root
[new-match] 0x559938e7c948 #469 #466 #2193 ; #2321 (#196 #196) (#2200 #2200)
[mk-app] #2359 >= #2281 #337
[mk-app] #2360 not #2359
[mk-app] #2361 I #2281
[mk-app] #2362 has_type #2361 #196
[mk-app] #2363 or #2360 #2362
[mk-app] #2364 not #469
[mk-app] #2365 or #2364 #2360 #2362
[instance] 0x559938e7c948 ; 2
[attach-enode] #2361 2
[attach-enode] #2362 2
[end-of-instance]
[assign] (not #2362) justification -1: -414 396
[attach-meaning] #366 arith (- 1)
[mk-app] #2366 * #366 #2281
[mk-app] #2367 + #2193 #2366
[mk-app] #2368 <= #2367 #337
[mk-app] #2369 >= #2367 #337
[attach-enode] #2366 0
[attach-enode] #2367 0
[assign] #2368 justification -1: 396
[assign] #2369 justification -1: 396
[assign] (not #2359) clause -443 444
[mk-app] #2370 = #2367 #337
[inst-discovered] theory-solving 0 arith#
[instance] 0 #2370
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2359
[resolve-lit] 0 (not #2368)
[resolve-process] #2359
[resolve-lit] 0 #2362
[resolve-process] (not #2368)
[conflict] #2362
[pop] 1 8
[attach-enode] #2361 0
[attach-enode] #2362 0
[assign] #2362 axiom
[assign] #2321 justification -1: 443 396
[new-match] 0x559938e7ca38 #518 #199 #2200 ; #2321 (#196 #196)
[new-match] 0x559938e7ca68 #203 #199 #2200 ; #2321 (#196 #196)
[new-match] 0x559938e7ca98 #469 #466 #2193 ; #2321 (#196 #196) (#2200 #2200)
[mk-app] #2366 or #2322 #2359
[mk-app] #2367 not #518
[mk-app] #2368 or #2367 #2322 #2359
[instance] 0x559938e7ca38 ; 2
[assign] #2359 justification -1: 70 414
[end-of-instance]
[assign] #2324 clause 415 -414
[attach-meaning] #366 arith (- 1)
[mk-app] #2369 * #366 #2281
[mk-app] #2364 + #2193 #2369
[mk-app] #2365 <= #2364 #337
[mk-app] #2370 >= #2364 #337
[attach-enode] #2369 0
[attach-enode] #2364 0
[assign] #2365 justification -1: 396
[assign] #2370 justification -1: 396
[eq-expl] #1213 root
[new-match] 0x559938e7cd58 #1191 #1190 #1213 #2200 ; #2323
[eq-expl] #1212 root
[new-match] 0x559938e7cd90 #1209 #1205 #1212 #2200 ; #2323 (#1213 #1213)
[mk-app] #2371 the_q!model.rec%pow2.? #2200 #1187
[mk-app] #2372 = #2323 #2371
[mk-app] #2373 not #1191
[mk-app] #2374 or #2373 #2372
[instance] 0x559938e7cd58 ; 2
[attach-enode] #1187 2
[attach-enode] #2371 2
[attach-enode] #2372 2
[assign] #2372 justification -1: 262
[end-of-instance]
[mk-app] #2375 = #2281 #337
[mk-app] #2376 Sub #2281 #292
[mk-app] #2377 nClip #2376
[mk-app] #2378 I #2377
[mk-app] #2379 the_q!model.rec%pow2.? #2378 #1212
[mk-app] #2380 Mul #1196 #2379
[mk-app] #2381 if #2375 #292 #2380
[mk-app] #2382 = #2323 #2381
[mk-app] #2383 or #2322 #2382
[mk-app] #2384 not #1209
[mk-app] #2385 or #2384 #2322 #2382
[instance] 0x559938e7cd90 ; 2
[mk-app] #2386 = #292 #2381
[mk-app] #2387 = #2380 #2381
[attach-enode] #2381 2
[attach-enode] #2375 2
[mk-app] #2388 = #337 #2281
[mk-app] #2389 <= #2281 #337
[attach-enode] #2388 2
[attach-enode] #2376 2
[attach-enode] #2377 2
[attach-enode] #2378 2
[attach-enode] #2379 2
[attach-enode] #2380 2
[attach-enode] #2386 2
[attach-enode] #2387 2
[attach-enode] #2382 2
[assign] #2382 justification -1: 263 414
[end-of-instance]
[mk-app] #2390 = #2364 #337
[inst-discovered] theory-solving 0 arith#
[instance] 0 #2390
[end-of-instance]
[eq-expl] #1187 root
[new-match] 0x559938e7d708 #1191 #1190 #1187 #2200 ; #2371
[decide-and-or] #2333 #2329
[push] 7
[assign] (not #2328) decision axiom
[new-match] 0x559938e7d780 #518 #199 #2204 ; #2328 (#196 #196)
[new-match] 0x559938e7d7b0 #203 #199 #2204 ; #2328 (#196 #196)
[eq-expl] #2203 lit #2286 ; #2285
[eq-expl] #2285 root
[new-match] 0x559938e7d7e0 #469 #466 #2203 ; #2328 (#196 #196) (#2204 #2204)
[mk-app] #2390 >= #2285 #337
[mk-app] #2391 not #2390
[mk-app] #2392 I #2285
[mk-app] #2393 has_type #2392 #196
[mk-app] #2394 or #2391 #2393
[mk-app] #2395 not #469
[mk-app] #2396 or #2395 #2391 #2393
[instance] 0x559938e7d7e0 ; 2
[attach-enode] #2392 2
[attach-enode] #2393 2
[end-of-instance]
[assign] (not #2393) justification -1: -416 397
[attach-meaning] #366 arith (- 1)
[mk-app] #2397 * #366 #2285
[mk-app] #2398 + #2203 #2397
[mk-app] #2399 <= #2398 #337
[mk-app] #2400 >= #2398 #337
[attach-enode] #2397 0
[attach-enode] #2398 0
[assign] #2399 justification -1: 397
[assign] #2400 justification -1: 397
[assign] (not #2390) clause -454 455
[mk-app] #2401 = #2398 #337
[inst-discovered] theory-solving 0 arith#
[instance] 0 #2401
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2390
[resolve-lit] 0 (not #2399)
[resolve-process] #2390
[resolve-lit] 0 #2393
[resolve-process] (not #2399)
[conflict] #2393
[pop] 1 8
[attach-enode] #2392 0
[attach-enode] #2393 0
[assign] #2393 axiom
[assign] #2328 justification -1: 454 397
[new-match] 0x559938e7d8d0 #518 #199 #2204 ; #2328 (#196 #196)
[new-match] 0x559938e7d900 #203 #199 #2204 ; #2328 (#196 #196)
[new-match] 0x559938e7d930 #469 #466 #2203 ; #2328 (#196 #196) (#2204 #2204)
[mk-app] #2397 or #2329 #2390
[mk-app] #2398 or #2367 #2329 #2390
[instance] 0x559938e7d8d0 ; 2
[assign] #2390 justification -1: 70 416
[end-of-instance]
[assign] #2331 clause 417 -416
[attach-meaning] #366 arith (- 1)
[mk-app] #2399 * #366 #2285
[mk-app] #2400 + #2203 #2399
[mk-app] #2395 <= #2400 #337
[mk-app] #2396 >= #2400 #337
[attach-enode] #2399 0
[attach-enode] #2400 0
[assign] #2395 justification -1: 397
[assign] #2396 justification -1: 397
[new-match] 0x559938e7dbf0 #1191 #1190 #1213 #2204 ; #2330
[new-match] 0x559938e7dc28 #1209 #1205 #1212 #2204 ; #2330 (#1213 #1213)
[mk-app] #2401 the_q!model.rec%pow2.? #2204 #1187
[mk-app] #2402 = #2330 #2401
[mk-app] #2403 or #2373 #2402
[instance] 0x559938e7dbf0 ; 2
[attach-enode] #2401 2
[attach-enode] #2402 2
[assign] #2402 justification -1: 262
[end-of-instance]
[mk-app] #2404 = #2285 #337
[mk-app] #2405 Sub #2285 #292
[mk-app] #2406 nClip #2405
[mk-app] #2407 I #2406
[mk-app] #2408 the_q!model.rec%pow2.? #2407 #1212
[mk-app] #2409 Mul #1196 #2408
[mk-app] #2410 if #2404 #292 #2409
[mk-app] #2411 = #2330 #2410
[mk-app] #2412 or #2329 #2411
[mk-app] #2413 or #2384 #2329 #2411
[instance] 0x559938e7dc28 ; 2
[mk-app] #2414 = #292 #2410
[mk-app] #2415 = #2409 #2410
[attach-enode] #2410 2
[attach-enode] #2404 2
[mk-app] #2416 = #337 #2285
[mk-app] #2417 <= #2285 #337
[attach-enode] #2416 2
[attach-enode] #2405 2
[attach-enode] #2406 2
[attach-enode] #2407 2
[attach-enode] #2408 2
[attach-enode] #2409 2
[attach-enode] #2414 2
[attach-enode] #2415 2
[attach-enode] #2411 2
[assign] #2411 justification -1: 263 416
[end-of-instance]
[mk-app] #2418 = #2400 #337
[inst-discovered] theory-solving 0 arith#
[instance] 0 #2418
[end-of-instance]
[new-match] 0x559938e7e530 #1191 #1190 #1187 #2204 ; #2401
[push] 7
[assign] (not #2388) decision axiom
[assign] (not #2389) clause -450 449
[assign] (not #2375) justification -1: -449
[assign] #2387 clause 452 448
[eq-expl] #2379 root
[new-match] 0x559938e7e5f0 #570 #564 #2379 #1196 ; #2380
[new-match] 0x559938e7e628 #1866 #564 #2379 #1196 ; #2380
[eq-expl] #2378 root
[new-match] 0x559938e7e660 #1191 #1190 #1212 #2378 ; #2379
[eq-expl] #2377 root
[new-match] 0x559938df7598 #170 #169 #2377 ; #2378
[eq-expl] #2376 root
[new-match] 0x559938df75c8 #1817 #344 #2376 ; #2377
[new-match] 0x559938df75f8 #563 #555 #292 #2281 ; #2376
[mk-app] #2418 * #2379 #1196
[mk-app] #2419 * #366 #2418
[mk-app] #2420 + #2380 #2419
[mk-app] #2421 = #2420 #337
[mk-app] #2422 * #1196 #2379
[inst-discovered] theory-solving 0 arith# ; #2418
[mk-app] #2423 = #2418 #2422
[instance] 0 #2423
[attach-enode] #2423 0
[end-of-instance]
[mk-app] #2423 Int
[attach-meaning] #2423 arith (- 2)
[mk-app] #2424 * #2423 #2379
[mk-app] #2425 * #366 #2422
[inst-discovered] theory-solving 0 arith# ; #2425
[mk-app] #2426 = #2425 #2424
[instance] 0 #2426
[attach-enode] #2426 0
[end-of-instance]
[mk-app] #2422 + #2424 #2380
[mk-app] #2425 + #2380 #2424
[inst-discovered] theory-solving 0 arith# ; #2425
[mk-app] #2426 = #2425 #2422
[instance] 0 #2426
[attach-enode] #2426 0
[end-of-instance]
[mk-app] #2425 * #1196 #2379
[attach-meaning] #366 arith (- 1)
[mk-app] #2426 * #366 #2380
[mk-app] #2427 + #2425 #2426
[mk-app] #2428 = #2427 #337
[mk-app] #2429 = #2422 #337
[inst-discovered] theory-solving 0 arith# ; #2429
[mk-app] #2430 = #2429 #2428
[instance] 0 #2430
[attach-enode] #2430 0
[end-of-instance]
[mk-app] #2423 or #2219 #2428
[instance] 0x559938e7e5f0 ; 3
[attach-enode] #2425 3
[attach-enode] #2426 3
[attach-enode] #2427 3
[attach-enode] #2428 3
[mk-app] #2424 = #337 #2427
[mk-app] #2422 <= #2427 #337
[mk-app] #2429 >= #2427 #337
[attach-enode] #2424 3
[assign] #2428 justification -1: 78
[end-of-instance]
[mk-app] #2430 >= #2379 #337
[mk-app] #2431 not #2430
[mk-app] #2432 >= #2380 #337
[mk-app] #2433 or #2245 #2431 #2432
[mk-app] #2434 or #2431 #2432
[mk-app] #2435 or #2 #2431 #2432
[inst-discovered] theory-solving 0 basic# ; #2435
[mk-app] #2436 = #2435 #2434
[instance] 0 #2436
[attach-enode] #2436 0
[end-of-instance]
[mk-app] #2435 or #2230 #2431 #2432
[instance] 0x559938e7e628 ; 3
[end-of-instance]
[mk-app] #2434 the_q!model.rec%pow2.? #2378 #1187
[mk-app] #2436 = #2379 #2434
[mk-app] #2437 or #2373 #2436
[instance] 0x559938e7e660 ; 3
[attach-enode] #2434 3
[attach-enode] #2436 3
[assign] #2436 justification -1: 262
[end-of-instance]
[mk-app] #2438 %I #2378
[mk-app] #2439 = #2377 #2438
[mk-app] #2440 or #2283 #2439
[instance] 0x559938df7598 ; 3
[attach-enode] #2438 3
[attach-enode] #2439 3
[assign] #2439 justification -1: 25
[end-of-instance]
[mk-app] #2441 >= #2377 #337
[mk-app] #2442 not #2441
[mk-app] #2443 >= #2376 #337
[mk-app] #2444 not #2443
[mk-app] #2445 = #2376 #2377
[mk-app] #2446 or #2444 #2445
[mk-app] #2447 not #2446
[mk-app] #2448 or #2442 #2447
[mk-app] #2449 not #2448
[mk-app] #2450 or #2297 #2449
[instance] 0x559938df75c8 ; 3
[attach-enode] #2445 3
[attach-meaning] #366 arith (- 1)
[mk-app] #2451 * #366 #2377
[mk-app] #2452 + #2376 #2451
[mk-app] #2453 <= #2452 #337
[mk-app] #2454 >= #2452 #337
[attach-enode] #2451 3
[attach-enode] #2452 3
[assign] (not #2448) justification -1: 55
[end-of-instance]
[mk-app] #2455 + #292 #2369 #2376
[mk-app] #2456 = #2455 #337
[attach-meaning] #366 arith (- 1)
[mk-app] #2457 + #2369 #2376
[attach-meaning] #366 arith (- 1)
[mk-app] #2458 * #366 #2376
[mk-app] #2459 + #2281 #2458
[mk-app] #2457 = #2459 #292
[inst-discovered] theory-solving 0 arith# ; #2456
[mk-app] #2460 = #2456 #2457
[instance] 0 #2460
[attach-enode] #2460 0
[end-of-instance]
[mk-app] #2460 or #2309 #2457
[instance] 0x559938df75f8 ; 3
[attach-enode] #2458 3
[attach-enode] #2459 3
[attach-enode] #2457 3
[mk-app] #2461 = #292 #2459
[mk-app] #2462 <= #2459 #292
[mk-app] #2463 >= #2459 #292
[attach-enode] #2461 3
[assign] #2457 justification -1: 77
[end-of-instance]
[assign] #2441 clause 473 479
[assign] #2446 clause 478 479
[assign] #2424 justification -1: 465
[assign] #2461 justification -1: 480
[mk-app] #2464 = #2201 #2380
[attach-meaning] #366 arith (- 1)
[mk-app] #2465 + #2201 #2426
[mk-app] #2466 <= #2465 #337
[mk-app] #2467 >= #2465 #337
[assign] #2464 justification -1: 415 452 453
[attach-enode] #2464 0
[attach-enode] #2465 0
[assign] #2466 justification -1: 484
[assign] #2467 justification -1: 484
[new-match] 0x559938df8618 #1191 #1190 #1187 #2378 ; #2434
[assign] #2422 clause 467 -466
[assign] #2429 clause 468 -466
[assign] #2462 clause 482 -481
[assign] #2463 clause 483 -481
[mk-app] #2468 = #2465 #337
[inst-discovered] theory-solving 0 arith#
[instance] 0 #2468
[end-of-instance]
[assign] (not #2430) clause -469 -467 378 -486
[assign] (not #2432) clause -470 -486 378
[assign] #2443 clause 474 450 -482
[assign] #2445 clause 475 -474 -478
[assign] #2453 clause 476 -475
[assign] #2454 clause 477 -475
[mk-app] #2468 = #2452 #337
[inst-discovered] theory-solving 0 arith#
[instance] 0 #2468
[end-of-instance]
[push] 8
[assign] (not #2416) decision axiom
[assign] (not #2417) clause -461 460
[assign] (not #2404) justification -1: -460
[assign] #2415 clause 463 459
[eq-expl] #2408 root
[new-match] 0x559938df8938 #570 #564 #2408 #1196 ; #2409
[new-match] 0x559938df8970 #1866 #564 #2408 #1196 ; #2409
[eq-expl] #2407 root
[new-match] 0x559938df89a8 #1191 #1190 #1212 #2407 ; #2408
[eq-expl] #2406 root
[new-match] 0x559938df89e0 #170 #169 #2406 ; #2407
[eq-expl] #2405 root
[new-match] 0x559938df8a10 #1817 #344 #2405 ; #2406
[new-match] 0x559938df8a40 #563 #555 #292 #2285 ; #2405
[mk-app] #2468 * #2408 #1196
[mk-app] #2469 * #366 #2468
[mk-app] #2470 + #2409 #2469
[mk-app] #2471 = #2470 #337
[mk-app] #2472 * #1196 #2408
[inst-discovered] theory-solving 0 arith# ; #2468
[mk-app] #2473 = #2468 #2472
[instance] 0 #2473
[attach-enode] #2473 0
[end-of-instance]
[mk-app] #2473 Int
[attach-meaning] #2473 arith (- 2)
[mk-app] #2474 * #2473 #2408
[mk-app] #2475 * #366 #2472
[inst-discovered] theory-solving 0 arith# ; #2475
[mk-app] #2476 = #2475 #2474
[instance] 0 #2476
[attach-enode] #2476 0
[end-of-instance]
[mk-app] #2472 + #2474 #2409
[mk-app] #2475 + #2409 #2474
[inst-discovered] theory-solving 0 arith# ; #2475
[mk-app] #2476 = #2475 #2472
[instance] 0 #2476
[attach-enode] #2476 0
[end-of-instance]
[mk-app] #2475 * #1196 #2408
[attach-meaning] #366 arith (- 1)
[mk-app] #2476 * #366 #2409
[mk-app] #2477 + #2475 #2476
[mk-app] #2478 = #2477 #337
[mk-app] #2479 = #2472 #337
[inst-discovered] theory-solving 0 arith# ; #2479
[mk-app] #2480 = #2479 #2478
[instance] 0 #2480
[attach-enode] #2480 0
[end-of-instance]
[mk-app] #2473 or #2219 #2478
[instance] 0x559938df8938 ; 3
[attach-enode] #2475 3
[attach-enode] #2476 3
[attach-enode] #2477 3
[attach-enode] #2478 3
[mk-app] #2474 = #337 #2477
[mk-app] #2472 <= #2477 #337
[mk-app] #2479 >= #2477 #337
[attach-enode] #2474 3
[assign] #2478 justification -1: 78
[end-of-instance]
[mk-app] #2480 >= #2408 #337
[mk-app] #2481 not #2480
[mk-app] #2482 >= #2409 #337
[mk-app] #2483 or #2245 #2481 #2482
[mk-app] #2484 or #2481 #2482
[mk-app] #2485 or #2 #2481 #2482
[inst-discovered] theory-solving 0 basic# ; #2485
[mk-app] #2486 = #2485 #2484
[instance] 0 #2486
[attach-enode] #2486 0
[end-of-instance]
[mk-app] #2485 or #2230 #2481 #2482
[instance] 0x559938df8970 ; 3
[end-of-instance]
[mk-app] #2484 the_q!model.rec%pow2.? #2407 #1187
[mk-app] #2486 = #2408 #2484
[mk-app] #2487 or #2373 #2486
[instance] 0x559938df89a8 ; 3
[attach-enode] #2484 3
[attach-enode] #2486 3
[assign] #2486 justification -1: 262
[end-of-instance]
[mk-app] #2488 %I #2407
[mk-app] #2489 = #2406 #2488
[mk-app] #2490 or #2283 #2489
[instance] 0x559938df89e0 ; 3
[attach-enode] #2488 3
[attach-enode] #2489 3
[assign] #2489 justification -1: 25
[end-of-instance]
[mk-app] #2491 >= #2406 #337
[mk-app] #2492 not #2491
[mk-app] #2493 >= #2405 #337
[mk-app] #2494 not #2493
[mk-app] #2495 = #2405 #2406
[mk-app] #2496 or #2494 #2495
[mk-app] #2497 not #2496
[mk-app] #2498 or #2492 #2497
[mk-app] #2499 not #2498
[mk-app] #2500 or #2297 #2499
[instance] 0x559938df8a10 ; 3
[attach-enode] #2495 3
[attach-meaning] #366 arith (- 1)
[mk-app] #2501 * #366 #2406
[mk-app] #2502 + #2405 #2501
[mk-app] #2503 <= #2502 #337
[mk-app] #2504 >= #2502 #337
[attach-enode] #2501 3
[attach-enode] #2502 3
[assign] (not #2498) justification -1: 55
[end-of-instance]
[mk-app] #2505 + #292 #2399 #2405
[mk-app] #2506 = #2505 #337
[attach-meaning] #366 arith (- 1)
[mk-app] #2507 + #2399 #2405
[attach-meaning] #366 arith (- 1)
[mk-app] #2508 * #366 #2405
[mk-app] #2509 + #2285 #2508
[mk-app] #2507 = #2509 #292
[inst-discovered] theory-solving 0 arith# ; #2506
[mk-app] #2510 = #2506 #2507
[instance] 0 #2510
[attach-enode] #2510 0
[end-of-instance]
[mk-app] #2510 or #2309 #2507
[instance] 0x559938df8a40 ; 3
[attach-enode] #2508 3
[attach-enode] #2509 3
[attach-enode] #2507 3
[mk-app] #2511 = #292 #2509
[mk-app] #2512 <= #2509 #292
[mk-app] #2513 >= #2509 #292
[attach-enode] #2511 3
[assign] #2507 justification -1: 77
[end-of-instance]
[assign] #2491 clause 495 501
[assign] #2496 clause 500 501
[assign] #2474 justification -1: 487
[assign] #2511 justification -1: 502
[mk-app] #2514 = #2205 #2409
[attach-meaning] #366 arith (- 1)
[mk-app] #2515 + #2205 #2476
[mk-app] #2516 <= #2515 #337
[mk-app] #2517 >= #2515 #337
[assign] #2514 justification -1: 417 463 464
[attach-enode] #2514 0
[attach-enode] #2515 0
[assign] #2516 justification -1: 506
[assign] #2517 justification -1: 506
[new-match] 0x559938e9a850 #1191 #1190 #1187 #2407 ; #2484
[assign] #2472 clause 489 -488
[assign] #2479 clause 490 -488
[assign] #2512 clause 504 -503
[assign] #2513 clause 505 -503
[mk-app] #2518 = #2515 #337
[inst-discovered] theory-solving 0 arith#
[instance] 0 #2518
[end-of-instance]
[assign] (not #2480) clause -491 -489 391 -508
[assign] (not #2482) clause -492 -508 391
[assign] #2493 clause 496 461 -504
[assign] #2495 clause 497 -496 -500
[assign] #2503 clause 498 -497
[assign] #2504 clause 499 -497
[mk-app] #2518 = #2502 #337
[inst-discovered] theory-solving 0 arith#
[instance] 0 #2518
[end-of-instance]
[mk-app] #2518 >= #2271 #292
[assign] #2518 justification -1: -378 -391
[resolve-process] true
[resolve-lit] 0 (not #2518)
[resolve-lit] 5 #2246
[conflict] (not #2518) #2246
[pop] 5 9
[attach-enode] #2376 0
[attach-enode] #2377 0
[attach-enode] #2378 0
[attach-enode] #2379 0
[attach-enode] #2380 0
[attach-enode] #2425 0
[attach-enode] #2426 0
[attach-enode] #2427 0
[attach-enode] #2465 0
[attach-enode] #2458 0
[attach-enode] #2459 0
[attach-enode] #2405 0
[attach-enode] #2406 0
[attach-enode] #2407 0
[attach-enode] #2408 0
[attach-enode] #2409 0
[attach-enode] #2475 0
[attach-enode] #2476 0
[attach-enode] #2477 0
[attach-enode] #2515 0
[attach-enode] #2508 0
[attach-enode] #2509 0
[attach-enode] #2361 0
[attach-enode] #2362 0
[assign] #2362 axiom
[attach-enode] #2392 0
[attach-enode] #2393 0
[assign] #2393 axiom
[assign] (not #2518) clause -459 385
[assign] #2321 justification -1: 457 396
[assign] #2328 justification -1: 458 397
[attach-meaning] #366 arith (- 1)
[mk-app] #2364 + #2193 #2369
[mk-app] #2365 <= #2364 #337
[mk-app] #2370 >= #2364 #337
[attach-enode] #2369 0
[attach-enode] #2364 0
[assign] #2365 justification -1: 396
[assign] #2370 justification -1: 396
[attach-meaning] #366 arith (- 1)
[mk-app] #2388 + #2203 #2399
[mk-app] #2386 <= #2388 #337
[mk-app] #2387 >= #2388 #337
[attach-enode] #2399 0
[attach-enode] #2388 0
[assign] #2386 justification -1: 397
[assign] #2387 justification -1: 397
[assign] #2324 clause 415 -414
[assign] #2331 clause 417 -416
[mk-app] #2400 = #2364 #337
[inst-discovered] theory-solving 0 arith#
[instance] 0 #2400
[end-of-instance]
[mk-app] #2400 = #2388 #337
[inst-discovered] theory-solving 0 arith#
[instance] 0 #2400
[end-of-instance]
[new-match] 0x559938e7dd90 #1191 #1190 #1213 #2200 ; #2323
[new-match] 0x559938e7ddc8 #1209 #1205 #1212 #2200 ; #2323 (#1213 #1213)
[new-match] 0x559938e7de00 #1191 #1190 #1213 #2204 ; #2330
[new-match] 0x559938e7de38 #1209 #1205 #1212 #2204 ; #2330 (#1213 #1213)
[mk-app] #2400 not #1191
[mk-app] #2395 or #2400 #2372
[instance] 0x559938e7dd90 ; 2
[attach-enode] #1187 2
[attach-enode] #2371 2
[attach-enode] #2372 2
[assign] #2372 justification -1: 262
[end-of-instance]
[mk-app] #2396 not #1209
[mk-app] #2416 or #2396 #2322 #2382
[instance] 0x559938e7ddc8 ; 2
[mk-app] #2414 = #292 #2381
[mk-app] #2415 = #2380 #2381
[attach-enode] #2381 2
[attach-enode] #2375 2
[mk-app] #2428 = #337 #2281
[attach-enode] #2428 2
[attach-enode] #2414 2
[attach-enode] #2415 2
[attach-enode] #2382 2
[assign] #2382 justification -1: 263 414
[end-of-instance]
[mk-app] #2424 or #2400 #2402
[instance] 0x559938e7de00 ; 2
[attach-enode] #2401 2
[attach-enode] #2402 2
[assign] #2402 justification -1: 262
[end-of-instance]
[mk-app] #2429 or #2396 #2329 #2411
[instance] 0x559938e7de38 ; 2
[mk-app] #2451 = #292 #2410
[mk-app] #2452 = #2409 #2410
[attach-enode] #2410 2
[attach-enode] #2404 2
[mk-app] #2453 = #337 #2285
[attach-enode] #2453 2
[attach-enode] #2451 2
[attach-enode] #2452 2
[attach-enode] #2411 2
[assign] #2411 justification -1: 263 416
[end-of-instance]
[eq-expl] #1187 root
[new-match] 0x559938df79a0 #1191 #1190 #1187 #2200 ; #2371
[new-match] 0x559938df79d8 #1191 #1190 #1187 #2204 ; #2401
[decide-and-or] #2267 #2264
[push] 4
[assign] (not #2263) decision axiom
[assign] (not #2226) clause -379 391 -390
[push] 5
[assign] (not #2292) decision axiom
[assign] (not #2290) clause -399 400
[assign] #2301 clause 401 399 -398
[assign] (not #2302) clause -402 399 -398
[push] 6
[assign] (not #2316) decision axiom
[assign] #2317 clause 410 409
[assign] (not #2228) clause -380 409 385 -384
[push] 7
[assign] (not #2428) decision axiom
[assign] (not #2375) justification -1: -466
[assign] #2415 clause 469 465
[mk-app] #2454 = #2201 #2380
[attach-meaning] #366 arith (- 1)
[mk-app] #2457 <= #2465 #337
[assign] #2454 justification -1: 415 469 470
[attach-enode] #2454 0
[assign] #2457 justification -1: 478
[assign] #2467 justification -1: 478
[eq-expl] #2379 root
[new-match] 0x559938df7c80 #570 #564 #2379 #1196 ; #2380
[new-match] 0x559938df7cb8 #1866 #564 #2379 #1196 ; #2380
[eq-expl] #2378 root
[new-match] 0x559938df7cf0 #1191 #1190 #1212 #2378 ; #2379
[eq-expl] #2377 root
[new-match] 0x559938df7d28 #170 #169 #2377 ; #2378
[eq-expl] #2376 root
[new-match] 0x559938df7d58 #1817 #344 #2376 ; #2377
[new-match] 0x559938df7d88 #563 #555 #292 #2281 ; #2376
[inst-discovered] theory-solving 0 arith# ; #2418
[mk-app] #2461 = #2418 #2425
[instance] 0 #2461
[attach-enode] #2461 0
[end-of-instance]
[mk-app] #2461 Int
[attach-meaning] #2461 arith (- 2)
[mk-app] #2463 * #2461 #2379
[mk-app] #2464 * #366 #2425
[inst-discovered] theory-solving 0 arith# ; #2464
[mk-app] #2466 = #2464 #2463
[instance] 0 #2466
[attach-enode] #2466 0
[end-of-instance]
[mk-app] #2464 + #2463 #2380
[mk-app] #2466 + #2380 #2463
[inst-discovered] theory-solving 0 arith# ; #2466
[mk-app] #2478 = #2466 #2464
[instance] 0 #2478
[attach-enode] #2478 0
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #2466 = #2427 #337
[mk-app] #2478 = #2464 #337
[inst-discovered] theory-solving 0 arith# ; #2478
[mk-app] #2474 = #2478 #2466
[instance] 0 #2474
[attach-enode] #2474 0
[end-of-instance]
[mk-app] #2461 or #2219 #2466
[instance] 0x559938df7c80 ; 3
[attach-enode] #2466 3
[mk-app] #2463 = #337 #2427
[mk-app] #2464 >= #2427 #337
[attach-enode] #2463 3
[assign] #2466 justification -1: 78
[end-of-instance]
[mk-app] #2478 or #2431 #2432
[mk-app] #2474 or #2 #2431 #2432
[inst-discovered] theory-solving 0 basic# ; #2474
[mk-app] #2479 = #2474 #2478
[instance] 0 #2479
[attach-enode] #2479 0
[end-of-instance]
[mk-app] #2474 or #2230 #2431 #2432
[instance] 0x559938df7cb8 ; 3
[end-of-instance]
[mk-app] #2478 or #2400 #2436
[instance] 0x559938df7cf0 ; 3
[attach-enode] #2434 3
[attach-enode] #2436 3
[assign] #2436 justification -1: 262
[end-of-instance]
[mk-app] #2479 or #2283 #2439
[instance] 0x559938df7d28 ; 3
[attach-enode] #2438 3
[attach-enode] #2439 3
[assign] #2439 justification -1: 25
[end-of-instance]
[mk-app] #2501 or #2297 #2449
[instance] 0x559938df7d58 ; 3
[attach-enode] #2445 3
[attach-meaning] #366 arith (- 1)
[mk-app] #2502 * #366 #2377
[mk-app] #2503 + #2376 #2502
[mk-app] #2504 <= #2503 #337
[mk-app] #2507 >= #2503 #337
[attach-enode] #2502 3
[attach-enode] #2503 3
[assign] (not #2448) justification -1: 55
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #2511 + #2369 #2376
[attach-meaning] #366 arith (- 1)
[mk-app] #2511 = #2459 #292
[inst-discovered] theory-solving 0 arith# ; #2456
[mk-app] #2513 = #2456 #2511
[instance] 0 #2513
[attach-enode] #2513 0
[end-of-instance]
[mk-app] #2513 or #2309 #2511
[instance] 0x559938df7d88 ; 3
[attach-enode] #2511 3
[mk-app] #2514 = #292 #2459
[mk-app] #2516 >= #2459 #292
[attach-enode] #2514 3
[assign] #2511 justification -1: 77
[end-of-instance]
[assign] (not #2432) clause -446 -445 378
[assign] #2441 clause 485 490
[assign] #2446 clause 489 490
[assign] (not #2430) clause -444 446
[assign] #2463 justification -1: 480
[assign] #2514 justification -1: 491
[mk-app] #2510 = #2465 #337
[inst-discovered] theory-solving 0 arith#
[instance] 0 #2510
[end-of-instance]
[new-match] 0x559938df88d8 #1191 #1190 #1187 #2378 ; #2434
[assign] #2422 clause 443 -481
[assign] #2464 clause 482 -481
[assign] #2462 clause 449 -492
[assign] #2516 clause 493 -492
[push] 8
[assign] (not #2389) decision axiom
[assign] #2443 clause 448 447 -449
[assign] #2359 clause 467 447
[assign] #2445 clause 486 -448 -489
[assign] #2504 clause 487 -486
[assign] #2507 clause 488 -486
[mk-app] #2510 = #2503 #337
[inst-discovered] theory-solving 0 arith#
[instance] 0 #2510
[end-of-instance]
[push] 9
[assign] (not #2453) decision axiom
[assign] (not #2404) justification -1: -473
[assign] #2452 clause 476 472
[mk-app] #2510 = #2205 #2409
[attach-meaning] #366 arith (- 1)
[mk-app] #2500 <= #2515 #337
[assign] #2510 justification -1: 417 476 477
[attach-enode] #2510 0
[assign] #2500 justification -1: 494
[assign] #2517 justification -1: 494
[eq-expl] #2408 root
[new-match] 0x559938df8c78 #570 #564 #2408 #1196 ; #2409
[new-match] 0x559938df8cb0 #1866 #564 #2408 #1196 ; #2409
[eq-expl] #2407 root
[new-match] 0x559938df8ce8 #1191 #1190 #1212 #2407 ; #2408
[eq-expl] #2406 root
[new-match] 0x559938df8d20 #170 #169 #2406 ; #2407
[eq-expl] #2405 root
[new-match] 0x559938df8d50 #1817 #344 #2405 ; #2406
[new-match] 0x559938df8d80 #563 #555 #292 #2285 ; #2405
[inst-discovered] theory-solving 0 arith# ; #2468
[mk-app] #2490 = #2468 #2475
[instance] 0 #2490
[attach-enode] #2490 0
[end-of-instance]
[mk-app] #2490 Int
[attach-meaning] #2490 arith (- 2)
[mk-app] #2373 * #2490 #2408
[mk-app] #2487 * #366 #2475
[inst-discovered] theory-solving 0 arith# ; #2487
[mk-app] #2485 = #2487 #2373
[instance] 0 #2485
[attach-enode] #2485 0
[end-of-instance]
[mk-app] #2487 + #2373 #2409
[mk-app] #2485 + #2409 #2373
[inst-discovered] theory-solving 0 arith# ; #2485
[mk-app] #2473 = #2485 #2487
[instance] 0 #2473
[attach-enode] #2473 0
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #2485 = #2477 #337
[mk-app] #2473 = #2487 #337
[inst-discovered] theory-solving 0 arith# ; #2473
[mk-app] #2460 = #2473 #2485
[instance] 0 #2460
[attach-enode] #2460 0
[end-of-instance]
[mk-app] #2490 or #2219 #2485
[instance] 0x559938df8c78 ; 3
[attach-enode] #2485 3
[mk-app] #2373 = #337 #2477
[mk-app] #2487 >= #2477 #337
[attach-enode] #2373 3
[assign] #2485 justification -1: 78
[end-of-instance]
[mk-app] #2473 or #2481 #2482
[mk-app] #2460 or #2 #2481 #2482
[inst-discovered] theory-solving 0 basic# ; #2460
[mk-app] #2450 = #2460 #2473
[instance] 0 #2450
[attach-enode] #2450 0
[end-of-instance]
[mk-app] #2460 or #2230 #2481 #2482
[instance] 0x559938df8cb0 ; 3
[end-of-instance]
[mk-app] #2473 or #2400 #2486
[instance] 0x559938df8ce8 ; 3
[attach-enode] #2484 3
[attach-enode] #2486 3
[assign] #2486 justification -1: 262
[end-of-instance]
[mk-app] #2450 or #2283 #2489
[instance] 0x559938df8d20 ; 3
[attach-enode] #2488 3
[attach-enode] #2489 3
[assign] #2489 justification -1: 25
[end-of-instance]
[mk-app] #2440 or #2297 #2499
[instance] 0x559938df8d50 ; 3
[attach-enode] #2495 3
[attach-meaning] #366 arith (- 1)
[mk-app] #2437 * #366 #2406
[mk-app] #2435 + #2405 #2437
[mk-app] #2423 <= #2435 #337
[mk-app] #2384 >= #2435 #337
[attach-enode] #2437 3
[attach-enode] #2435 3
[assign] (not #2498) justification -1: 55
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #2413 + #2399 #2405
[attach-meaning] #366 arith (- 1)
[mk-app] #2413 = #2509 #292
[inst-discovered] theory-solving 0 arith# ; #2506
[mk-app] #2403 = #2506 #2413
[instance] 0 #2403
[attach-enode] #2403 0
[end-of-instance]
[mk-app] #2403 or #2309 #2413
[instance] 0x559938df8d80 ; 3
[attach-enode] #2413 3
[mk-app] #2367 = #292 #2509
[mk-app] #2398 >= #2509 #292
[attach-enode] #2367 3
[assign] #2413 justification -1: 77
[end-of-instance]
[assign] (not #2482) clause -453 -452 391
[assign] #2491 clause 501 506
[assign] #2496 clause 505 506
[assign] (not #2480) clause -451 453
[assign] #2373 justification -1: 496
[assign] #2367 justification -1: 507
[mk-app] #2385 = #2515 #337
[inst-discovered] theory-solving 0 arith#
[instance] 0 #2385
[end-of-instance]
[new-match] 0x559938e9a6d8 #1191 #1190 #1187 #2407 ; #2484
[assign] #2472 clause 450 -497
[assign] #2487 clause 498 -497
[assign] #2512 clause 456 -508
[assign] #2398 clause 509 -508
[push] 10
[assign] (not #2417) decision axiom
[assign] #2493 clause 455 454 -456
[assign] #2390 clause 474 454
[assign] #2495 clause 502 -455 -505
[assign] #2423 clause 503 -502
[assign] #2384 clause 504 -502
[mk-app] #2385 = #2435 #337
[inst-discovered] theory-solving 0 arith#
[instance] 0 #2385
[end-of-instance]
[resolve-process] true
[resolve-lit] 2 #2224
[resolve-lit] 0 #2263
[resolve-lit] 1 #2518
[conflict] #2263 #2224 #2518
[pop] 7 11
[assign] #2263 clause 391 459 378
[assign] #2226 clause 379 -391
[push] 4
[assign] (not #2292) decision axiom
[assign] (not #2290) clause -399 400
[assign] #2301 clause 401 399 -398
[assign] (not #2302) clause -402 399 -398
[push] 5
[assign] (not #2316) decision axiom
[assign] #2317 clause 410 409
[assign] (not #2228) clause -380 409 385 -384
[push] 6
[assign] (not #2428) decision axiom
[assign] (not #2375) justification -1: -466
[assign] #2415 clause 469 465
[mk-app] #2454 = #2201 #2380
[attach-meaning] #366 arith (- 1)
[mk-app] #2457 <= #2465 #337
[assign] #2454 justification -1: 415 469 470
[attach-enode] #2454 0
[assign] #2457 justification -1: 478
[assign] #2467 justification -1: 478
[eq-expl] #2379 root
[new-match] 0x559938df7c68 #570 #564 #2379 #1196 ; #2380
[new-match] 0x559938df7ca0 #1866 #564 #2379 #1196 ; #2380
[new-match] 0x559938df7cd8 #1191 #1190 #1212 #2378 ; #2379
[eq-expl] #2377 root
[new-match] 0x559938df7d10 #170 #169 #2377 ; #2378
[eq-expl] #2376 root
[new-match] 0x559938df7d40 #1817 #344 #2376 ; #2377
[new-match] 0x559938df7d70 #563 #555 #292 #2281 ; #2376
[inst-discovered] theory-solving 0 arith# ; #2418
[mk-app] #2466 = #2418 #2425
[instance] 0 #2466
[attach-enode] #2466 0
[end-of-instance]
[mk-app] #2466 Int
[attach-meaning] #2466 arith (- 2)
[mk-app] #2463 * #2466 #2379
[mk-app] #2464 * #366 #2425
[inst-discovered] theory-solving 0 arith# ; #2464
[mk-app] #2502 = #2464 #2463
[instance] 0 #2502
[attach-enode] #2502 0
[end-of-instance]
[mk-app] #2464 + #2463 #2380
[mk-app] #2502 + #2380 #2463
[inst-discovered] theory-solving 0 arith# ; #2502
[mk-app] #2503 = #2502 #2464
[instance] 0 #2503
[attach-enode] #2503 0
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #2502 = #2427 #337
[mk-app] #2503 = #2464 #337
[inst-discovered] theory-solving 0 arith# ; #2503
[mk-app] #2504 = #2503 #2502
[instance] 0 #2504
[attach-enode] #2504 0
[end-of-instance]
[mk-app] #2466 or #2219 #2502
[instance] 0x559938df7c68 ; 3
[attach-enode] #2502 3
[mk-app] #2463 = #337 #2427
[mk-app] #2464 >= #2427 #337
[attach-enode] #2463 3
[assign] #2502 justification -1: 78
[end-of-instance]
[mk-app] #2503 or #2431 #2432
[mk-app] #2504 or #2 #2431 #2432
[inst-discovered] theory-solving 0 basic# ; #2504
[mk-app] #2507 = #2504 #2503
[instance] 0 #2507
[attach-enode] #2507 0
[end-of-instance]
[mk-app] #2504 or #2230 #2431 #2432
[instance] 0x559938df7ca0 ; 3
[end-of-instance]
[mk-app] #2503 or #2400 #2436
[instance] 0x559938df7cd8 ; 3
[attach-enode] #2434 3
[attach-enode] #2436 3
[assign] #2436 justification -1: 262
[end-of-instance]
[mk-app] #2507 or #2283 #2439
[instance] 0x559938df7d10 ; 3
[attach-enode] #2438 3
[attach-enode] #2439 3
[assign] #2439 justification -1: 25
[end-of-instance]
[mk-app] #2511 or #2297 #2449
[instance] 0x559938df7d40 ; 3
[attach-enode] #2445 3
[attach-meaning] #366 arith (- 1)
[mk-app] #2514 * #366 #2377
[mk-app] #2516 + #2376 #2514
[mk-app] #2510 <= #2516 #337
[mk-app] #2500 >= #2516 #337
[attach-enode] #2514 3
[attach-enode] #2516 3
[assign] (not #2448) justification -1: 55
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #2485 + #2369 #2376
[attach-meaning] #366 arith (- 1)
[mk-app] #2485 = #2459 #292
[inst-discovered] theory-solving 0 arith# ; #2456
[mk-app] #2373 = #2456 #2485
[instance] 0 #2373
[attach-enode] #2373 0
[end-of-instance]
[mk-app] #2373 or #2309 #2485
[instance] 0x559938df7d70 ; 3
[attach-enode] #2485 3
[mk-app] #2487 = #292 #2459
[mk-app] #2437 >= #2459 #292
[attach-enode] #2487 3
[assign] #2485 justification -1: 77
[end-of-instance]
[assign] (not #2432) clause -446 -445 378
[assign] #2441 clause 485 490
[assign] #2446 clause 489 490
[assign] (not #2430) clause -444 446
[assign] #2463 justification -1: 480
[assign] #2487 justification -1: 491
[mk-app] #2435 = #2465 #337
[inst-discovered] theory-solving 0 arith#
[instance] 0 #2435
[end-of-instance]
[new-match] 0x559938df88c0 #1191 #1190 #1187 #2378 ; #2434
[assign] #2422 clause 443 -481
[assign] #2464 clause 482 -481
[assign] #2462 clause 449 -492
[assign] #2437 clause 493 -492
[push] 7
[assign] (not #2389) decision axiom
[assign] #2443 clause 448 447 -449
[assign] #2359 clause 467 447
[assign] #2445 clause 486 -448 -489
[assign] #2510 clause 487 -486
[assign] #2500 clause 488 -486
[mk-app] #2435 = #2516 #337
[inst-discovered] theory-solving 0 arith#
[instance] 0 #2435
[end-of-instance]
[push] 8
[assign] (not #2453) decision axiom
[assign] (not #2404) justification -1: -473
[assign] #2452 clause 476 472
[mk-app] #2435 = #2205 #2409
[attach-meaning] #366 arith (- 1)
[mk-app] #2423 <= #2515 #337
[assign] #2435 justification -1: 417 476 477
[attach-enode] #2435 0
[assign] #2423 justification -1: 494
[assign] #2517 justification -1: 494
[eq-expl] #2408 root
[new-match] 0x559938df8c60 #570 #564 #2408 #1196 ; #2409
[new-match] 0x559938df8c98 #1866 #564 #2408 #1196 ; #2409
[new-match] 0x559938df8cd0 #1191 #1190 #1212 #2407 ; #2408
[eq-expl] #2406 root
[new-match] 0x559938df8d08 #170 #169 #2406 ; #2407
[eq-expl] #2405 root
[new-match] 0x559938df8d38 #1817 #344 #2405 ; #2406
[new-match] 0x559938df8d68 #563 #555 #292 #2285 ; #2405
[inst-discovered] theory-solving 0 arith# ; #2468
[mk-app] #2384 = #2468 #2475
[instance] 0 #2384
[attach-enode] #2384 0
[end-of-instance]
[mk-app] #2384 Int
[attach-meaning] #2384 arith (- 2)
[mk-app] #2413 * #2384 #2408
[mk-app] #2367 * #366 #2475
[inst-discovered] theory-solving 0 arith# ; #2367
[mk-app] #2398 = #2367 #2413
[instance] 0 #2398
[attach-enode] #2398 0
[end-of-instance]
[mk-app] #2367 + #2413 #2409
[mk-app] #2398 + #2409 #2413
[inst-discovered] theory-solving 0 arith# ; #2398
[mk-app] #2403 = #2398 #2367
[instance] 0 #2403
[attach-enode] #2403 0
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #2398 = #2477 #337
[mk-app] #2403 = #2367 #337
[inst-discovered] theory-solving 0 arith# ; #2403
[mk-app] #2440 = #2403 #2398
[instance] 0 #2440
[attach-enode] #2440 0
[end-of-instance]
[mk-app] #2384 or #2219 #2398
[instance] 0x559938df8c60 ; 3
[attach-enode] #2398 3
[mk-app] #2413 = #337 #2477
[mk-app] #2367 >= #2477 #337
[attach-enode] #2413 3
[assign] #2398 justification -1: 78
[end-of-instance]
[mk-app] #2403 or #2481 #2482
[mk-app] #2440 or #2 #2481 #2482
[inst-discovered] theory-solving 0 basic# ; #2440
[mk-app] #2450 = #2440 #2403
[instance] 0 #2450
[attach-enode] #2450 0
[end-of-instance]
[mk-app] #2440 or #2230 #2481 #2482
[instance] 0x559938df8c98 ; 3
[end-of-instance]
[mk-app] #2403 or #2400 #2486
[instance] 0x559938df8cd0 ; 3
[attach-enode] #2484 3
[attach-enode] #2486 3
[assign] #2486 justification -1: 262
[end-of-instance]
[mk-app] #2450 or #2283 #2489
[instance] 0x559938df8d08 ; 3
[attach-enode] #2488 3
[attach-enode] #2489 3
[assign] #2489 justification -1: 25
[end-of-instance]
[mk-app] #2473 or #2297 #2499
[instance] 0x559938df8d38 ; 3
[attach-enode] #2495 3
[attach-meaning] #366 arith (- 1)
[mk-app] #2460 * #366 #2406
[mk-app] #2490 + #2405 #2460
[mk-app] #2513 <= #2490 #337
[mk-app] #2501 >= #2490 #337
[attach-enode] #2460 3
[attach-enode] #2490 3
[assign] (not #2498) justification -1: 55
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #2479 + #2399 #2405
[attach-meaning] #366 arith (- 1)
[mk-app] #2479 = #2509 #292
[inst-discovered] theory-solving 0 arith# ; #2506
[mk-app] #2478 = #2506 #2479
[instance] 0 #2478
[attach-enode] #2478 0
[end-of-instance]
[mk-app] #2478 or #2309 #2479
[instance] 0x559938df8d68 ; 3
[attach-enode] #2479 3
[mk-app] #2474 = #292 #2509
[mk-app] #2461 >= #2509 #292
[attach-enode] #2474 3
[assign] #2479 justification -1: 77
[end-of-instance]
[assign] #2491 clause 501 506
[assign] #2496 clause 505 506
[assign] #2413 justification -1: 496
[assign] #2474 justification -1: 507
[mk-app] #2385 = #2515 #337
[inst-discovered] theory-solving 0 arith#
[instance] 0 #2385
[end-of-instance]
[assign] #2482 clause 453 -495 -379 -390
[new-match] 0x559938e9a6f0 #1191 #1190 #1187 #2407 ; #2484
[assign] #2472 clause 450 -497
[assign] #2367 clause 498 -497
[assign] #2512 clause 456 -508
[assign] #2461 clause 509 -508
[assign] #2480 clause 451 -495 -379 -390 -498
[push] 9
[assign] (not #2417) decision axiom
[assign] #2493 clause 455 454 -456
[assign] #2390 clause 474 454
[assign] #2495 clause 502 -455 -505
[assign] #2513 clause 503 -502
[assign] #2501 clause 504 -502
[mk-app] #2385 = #2490 #337
[inst-discovered] theory-solving 0 arith#
[instance] 0 #2385
[end-of-instance]
[resolve-process] true
[resolve-lit] 1 #2316
[resolve-lit] 0 (not #2422)
[resolve-lit] 0 (not #2467)
[resolve-lit] 0 (not #2457)
[resolve-lit] 0 (not #2464)
[resolve-process] (not #2464)
[resolve-lit] 0 (not #2463)
[resolve-process] (not #2422)
[resolve-process] (not #2463)
[resolve-lit] 0 (not #2502)
[resolve-process] (not #2502)
[resolve-process] (not #2467)
[resolve-lit] 0 (not #2454)
[resolve-process] (not #2457)
[conflict] (not #2454) #2316
[pop] 4 10
[attach-enode] #2454 0
[attach-meaning] #366 arith (- 1)
[mk-app] #2457 <= #2465 #337
[assign] (not #2454) clause -480 409
[assign] (not #2415) justification -1: -480 415 470
[eq-expl] #2379 root
[new-match] 0x559938df7c10 #570 #564 #2379 #1196 ; #2380
[new-match] 0x559938df7c48 #1866 #564 #2379 #1196 ; #2380
[new-match] 0x559938df7c80 #1191 #1190 #1212 #2378 ; #2379
[eq-expl] #2377 root
[new-match] 0x559938df7cb8 #170 #169 #2377 ; #2378
[eq-expl] #2376 root
[new-match] 0x559938df7ce8 #1817 #344 #2376 ; #2377
[new-match] 0x559938df7d18 #563 #555 #292 #2281 ; #2376
[inst-discovered] theory-solving 0 arith# ; #2418
[mk-app] #2502 = #2418 #2425
[instance] 0 #2502
[attach-enode] #2502 0
[end-of-instance]
[mk-app] #2502 Int
[attach-meaning] #2502 arith (- 2)
[mk-app] #2463 * #2502 #2379
[mk-app] #2464 * #366 #2425
[inst-discovered] theory-solving 0 arith# ; #2464
[mk-app] #2514 = #2464 #2463
[instance] 0 #2514
[attach-enode] #2514 0
[end-of-instance]
[mk-app] #2464 + #2463 #2380
[mk-app] #2514 + #2380 #2463
[inst-discovered] theory-solving 0 arith# ; #2514
[mk-app] #2516 = #2514 #2464
[instance] 0 #2516
[attach-enode] #2516 0
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #2514 = #2427 #337
[mk-app] #2516 = #2464 #337
[inst-discovered] theory-solving 0 arith# ; #2516
[mk-app] #2510 = #2516 #2514
[instance] 0 #2510
[attach-enode] #2510 0
[end-of-instance]
[mk-app] #2502 or #2219 #2514
[instance] 0x559938df7c10 ; 3
[attach-enode] #2514 3
[mk-app] #2463 = #337 #2427
[mk-app] #2464 >= #2427 #337
[attach-enode] #2463 3
[assign] #2514 justification -1: 78
[end-of-instance]
[mk-app] #2516 or #2431 #2432
[mk-app] #2510 or #2 #2431 #2432
[inst-discovered] theory-solving 0 basic# ; #2510
[mk-app] #2500 = #2510 #2516
[instance] 0 #2500
[attach-enode] #2500 0
[end-of-instance]
[mk-app] #2510 or #2230 #2431 #2432
[instance] 0x559938df7c48 ; 3
[end-of-instance]
[mk-app] #2516 or #2400 #2436
[instance] 0x559938df7c80 ; 3
[attach-enode] #2434 3
[attach-enode] #2436 3
[assign] #2436 justification -1: 262
[end-of-instance]
[mk-app] #2500 or #2283 #2439
[instance] 0x559938df7cb8 ; 3
[attach-enode] #2438 3
[attach-enode] #2439 3
[assign] #2439 justification -1: 25
[end-of-instance]
[mk-app] #2485 or #2297 #2449
[instance] 0x559938df7ce8 ; 3
[attach-enode] #2445 3
[attach-meaning] #366 arith (- 1)
[mk-app] #2487 * #366 #2377
[mk-app] #2437 + #2376 #2487
[mk-app] #2435 <= #2437 #337
[mk-app] #2398 >= #2437 #337
[attach-enode] #2487 3
[attach-enode] #2437 3
[assign] (not #2448) justification -1: 55
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #2413 + #2369 #2376
[attach-meaning] #366 arith (- 1)
[mk-app] #2413 = #2459 #292
[inst-discovered] theory-solving 0 arith# ; #2456
[mk-app] #2460 = #2456 #2413
[instance] 0 #2460
[attach-enode] #2460 0
[end-of-instance]
[mk-app] #2460 or #2309 #2413
[instance] 0x559938df7d18 ; 3
[attach-enode] #2413 3
[mk-app] #2490 = #292 #2459
[mk-app] #2513 >= #2459 #292
[attach-enode] #2490 3
[assign] #2413 justification -1: 77
[end-of-instance]
[assign] #2375 clause 465 469
[assign] #2441 clause 487 492
[assign] #2446 clause 491 492
[assign] #2414 clause 468 -465
[assign] #2428 justification -1: 465
[assign] #2463 justification -1: 482
[assign] #2490 justification -1: 493
[mk-app] #2501 = #292 #2201
[mk-app] #2479 <= #2201 #292
[mk-app] #2474 >= #2201 #292
[assign] #2501 justification -1: 415 470 468
[attach-enode] #2501 0
[assign] #2479 justification -1: -378
[assign] (not #2474) justification -1: -378
[resolve-process] true
[resolve-lit] 0 (not #2501)
[resolve-lit] 0 #2474
[resolve-process] #2474
[resolve-lit] 3 #2224
[conflict] (not #2501) #2224
[pop] 3 6
[attach-enode] #2376 0
[attach-enode] #2377 0
[attach-enode] #2378 0
[attach-enode] #2379 0
[attach-enode] #2380 0
[attach-enode] #2425 0
[attach-enode] #2426 0
[attach-enode] #2427 0
[attach-enode] #2465 0
[attach-enode] #2458 0
[attach-enode] #2459 0
[attach-enode] #2405 0
[attach-enode] #2406 0
[attach-enode] #2407 0
[attach-enode] #2408 0
[attach-enode] #2409 0
[attach-enode] #2475 0
[attach-enode] #2476 0
[attach-enode] #2477 0
[attach-enode] #2515 0
[attach-enode] #2508 0
[attach-enode] #2509 0
[attach-enode] #2454 0
[attach-meaning] #366 arith (- 1)
[mk-app] #2364 <= #2465 #337
[attach-enode] #2361 0
[attach-enode] #2362 0
[assign] #2362 axiom
[attach-enode] #2392 0
[attach-enode] #2393 0
[assign] #2393 axiom
[attach-enode] #2501 0
[mk-app] #2365 <= #2201 #292
[mk-app] #2370 >= #2201 #292
[assign] #2365 justification -1: -378
[assign] (not #2370) justification -1: -378
[assign] (not #2501) justification -1: -466
[assign] #2321 justification -1: 462 396
[assign] #2328 justification -1: 463 397
[attach-meaning] #366 arith (- 1)
[mk-app] #2388 + #2193 #2369
[mk-app] #2386 <= #2388 #337
[mk-app] #2387 >= #2388 #337
[attach-enode] #2369 0
[attach-enode] #2388 0
[assign] #2386 justification -1: 396
[assign] #2387 justification -1: 396
[attach-meaning] #366 arith (- 1)
[mk-app] #2428 + #2203 #2399
[mk-app] #2414 <= #2428 #337
[mk-app] #2415 >= #2428 #337
[attach-enode] #2399 0
[attach-enode] #2428 0
[assign] #2414 justification -1: 397
[assign] #2415 justification -1: 397
[assign] #2324 clause 415 -414
[assign] #2331 clause 417 -416
[mk-app] #2453 = #2388 #337
[inst-discovered] theory-solving 0 arith#
[instance] 0 #2453
[end-of-instance]
[mk-app] #2453 = #2428 #337
[inst-discovered] theory-solving 0 arith#
[instance] 0 #2453
[end-of-instance]
[new-match] 0x559938e7e018 #1191 #1190 #1213 #2200 ; #2323
[new-match] 0x559938e7e050 #1209 #1205 #1212 #2200 ; #2323 (#1213 #1213)
[new-match] 0x559938e7e088 #1191 #1190 #1213 #2204 ; #2330
[new-match] 0x559938e7e0c0 #1209 #1205 #1212 #2204 ; #2330 (#1213 #1213)
[mk-app] #2453 not #1191
[mk-app] #2451 or #2453 #2372
[instance] 0x559938e7e018 ; 2
[attach-enode] #1187 2
[attach-enode] #2371 2
[attach-enode] #2372 2
[assign] #2372 justification -1: 262
[end-of-instance]
[mk-app] #2452 not #1209
[mk-app] #2457 or #2452 #2322 #2382
[instance] 0x559938e7e050 ; 2
[mk-app] #2514 = #292 #2381
[mk-app] #2463 = #2380 #2381
[attach-enode] #2381 2
[attach-enode] #2375 2
[mk-app] #2464 = #337 #2281
[attach-enode] #2464 2
[attach-enode] #2514 2
[attach-enode] #2463 2
[attach-enode] #2382 2
[assign] #2382 justification -1: 263 414
[end-of-instance]
[mk-app] #2487 or #2453 #2402
[instance] 0x559938e7e088 ; 2
[attach-enode] #2401 2
[attach-enode] #2402 2
[assign] #2402 justification -1: 262
[end-of-instance]
[mk-app] #2437 or #2452 #2329 #2411
[instance] 0x559938e7e0c0 ; 2
[mk-app] #2435 = #292 #2410
[mk-app] #2398 = #2409 #2410
[attach-enode] #2410 2
[attach-enode] #2404 2
[mk-app] #2413 = #337 #2285
[attach-enode] #2413 2
[attach-enode] #2435 2
[attach-enode] #2398 2
[attach-enode] #2411 2
[assign] #2411 justification -1: 263 416
[end-of-instance]
[assign] (not #2514) justification -1: -464 415 477
[eq-expl] #1187 root
[new-match] 0x559938df7c70 #1191 #1190 #1187 #2200 ; #2371
[new-match] 0x559938df7ca8 #1191 #1190 #1187 #2204 ; #2401
[assign] (not #2375) clause -472 475
[assign] #2463 clause 476 472
[assign] (not #2464) justification -1: -472
[assign] #2454 justification -1: 476 415 477
[eq-expl] #2379 root
[new-match] 0x559938df7d48 #570 #564 #2379 #1196 ; #2380
[new-match] 0x559938df7d80 #1866 #564 #2379 #1196 ; #2380
[eq-expl] #2378 root
[new-match] 0x559938df7db8 #1191 #1190 #1212 #2378 ; #2379
[eq-expl] #2377 root
[new-match] 0x559938df7df0 #170 #169 #2377 ; #2378
[eq-expl] #2376 root
[new-match] 0x559938df7e20 #1817 #344 #2376 ; #2377
[eq-expl] #2281 root
[new-match] 0x559938df7e50 #563 #555 #292 #2281 ; #2376
[inst-discovered] theory-solving 0 arith# ; #2418
[mk-app] #2490 = #2418 #2425
[instance] 0 #2490
[attach-enode] #2490 0
[end-of-instance]
[mk-app] #2490 Int
[attach-meaning] #2490 arith (- 2)
[mk-app] #2513 * #2490 #2379
[mk-app] #2479 * #366 #2425
[inst-discovered] theory-solving 0 arith# ; #2479
[mk-app] #2474 = #2479 #2513
[instance] 0 #2474
[attach-enode] #2474 0
[end-of-instance]
[mk-app] #2479 + #2513 #2380
[mk-app] #2474 + #2380 #2513
[inst-discovered] theory-solving 0 arith# ; #2474
[mk-app] #2460 = #2474 #2479
[instance] 0 #2460
[attach-enode] #2460 0
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #2474 = #2427 #337
[mk-app] #2460 = #2479 #337
[inst-discovered] theory-solving 0 arith# ; #2460
[mk-app] #2485 = #2460 #2474
[instance] 0 #2485
[attach-enode] #2485 0
[end-of-instance]
[mk-app] #2490 or #2219 #2474
[instance] 0x559938df7d48 ; 3
[attach-enode] #2474 3
[mk-app] #2513 = #337 #2427
[mk-app] #2479 >= #2427 #337
[attach-enode] #2513 3
[assign] #2474 justification -1: 78
[end-of-instance]
[mk-app] #2460 or #2431 #2432
[mk-app] #2485 or #2 #2431 #2432
[inst-discovered] theory-solving 0 basic# ; #2485
[mk-app] #2500 = #2485 #2460
[instance] 0 #2500
[attach-enode] #2500 0
[end-of-instance]
[mk-app] #2485 or #2230 #2431 #2432
[instance] 0x559938df7d80 ; 3
[end-of-instance]
[mk-app] #2460 or #2453 #2436
[instance] 0x559938df7db8 ; 3
[attach-enode] #2434 3
[attach-enode] #2436 3
[assign] #2436 justification -1: 262
[end-of-instance]
[mk-app] #2500 or #2283 #2439
[instance] 0x559938df7df0 ; 3
[attach-enode] #2438 3
[attach-enode] #2439 3
[assign] #2439 justification -1: 25
[end-of-instance]
[mk-app] #2400 or #2297 #2449
[instance] 0x559938df7e20 ; 3
[attach-enode] #2445 3
[attach-meaning] #366 arith (- 1)
[mk-app] #2516 * #366 #2377
[mk-app] #2510 + #2376 #2516
[mk-app] #2502 <= #2510 #337
[mk-app] #2396 >= #2510 #337
[attach-enode] #2516 3
[attach-enode] #2510 3
[assign] (not #2448) justification -1: 55
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #2429 + #2369 #2376
[attach-meaning] #366 arith (- 1)
[mk-app] #2429 = #2459 #292
[inst-discovered] theory-solving 0 arith# ; #2456
[mk-app] #2424 = #2456 #2429
[instance] 0 #2424
[attach-enode] #2424 0
[end-of-instance]
[mk-app] #2424 or #2309 #2429
[instance] 0x559938df7e50 ; 3
[attach-enode] #2429 3
[mk-app] #2416 = #292 #2459
[mk-app] #2395 >= #2459 #292
[attach-enode] #2416 3
[assign] #2429 justification -1: 77
[end-of-instance]
[assign] #2364 clause 461 -460
[assign] #2467 clause 445 -460
[assign] #2316 clause 409 -460
[assign] #2441 clause 490 495
[assign] #2446 clause 494 495
[assign] (not #2432) clause -446 -445 378
[assign] (not #2317) clause -410 -409
[assign] (not #2430) clause -444 446
[assign] #2513 justification -1: 485
[assign] #2416 justification -1: 496
[mk-app] #2461 = #2465 #337
[inst-discovered] theory-solving 0 arith#
[instance] 0 #2461
[end-of-instance]
[new-match] 0x559938df89b8 #1191 #1190 #1187 #2378 ; #2434
[assign] #2422 clause 443 -486
[assign] #2479 clause 487 -486
[assign] #2462 clause 449 -497
[assign] #2395 clause 498 -497
[decide-and-or] #2251 #2247
[push] 3
[assign] (not #2246) decision axiom
[assign] (not #2248) clause -386 385 -384
[assign] (not #2518) clause -457 385
[assign] #2263 clause 391 457 378
[assign] #2226 clause 379 -391
[push] 4
[assign] (not #2292) decision axiom
[assign] (not #2290) clause -399 400
[assign] #2301 clause 401 399 -398
[assign] (not #2302) clause -402 399 -398
[push] 5
[assign] (not #2389) decision axiom
[assign] #2443 clause 448 447 -449
[assign] #2359 clause 474 447
[assign] #2445 clause 491 -448 -494
[assign] #2502 clause 492 -491
[assign] #2396 clause 493 -491
[mk-app] #2461 = #2510 #337
[inst-discovered] theory-solving 0 arith#
[instance] 0 #2461
[end-of-instance]
[push] 6
[assign] (not #2413) decision axiom
[assign] (not #2404) justification -1: -480
[assign] #2398 clause 483 479
[mk-app] #2461 = #2205 #2409
[attach-meaning] #366 arith (- 1)
[assign] #2461 justification -1: 417 483 484
[attach-enode] #2461 0
[assign] #2423 justification -1: 499
[assign] #2517 justification -1: 499
[eq-expl] #2408 root
[new-match] 0x559938df8db0 #570 #564 #2408 #1196 ; #2409
[new-match] 0x559938df8de8 #1866 #564 #2408 #1196 ; #2409
[eq-expl] #2407 root
[new-match] 0x559938df8e20 #1191 #1190 #1212 #2407 ; #2408
[eq-expl] #2406 root
[new-match] 0x559938df8e58 #170 #169 #2406 ; #2407
[eq-expl] #2405 root
[new-match] 0x559938df8e88 #1817 #344 #2405 ; #2406
[new-match] 0x559938df8eb8 #563 #555 #292 #2285 ; #2405
[inst-discovered] theory-solving 0 arith# ; #2468
[mk-app] #2478 = #2468 #2475
[instance] 0 #2478
[attach-enode] #2478 0
[end-of-instance]
[mk-app] #2478 Int
[attach-meaning] #2478 arith (- 2)
[mk-app] #2473 * #2478 #2408
[mk-app] #2450 * #366 #2475
[inst-discovered] theory-solving 0 arith# ; #2450
[mk-app] #2403 = #2450 #2473
[instance] 0 #2403
[attach-enode] #2403 0
[end-of-instance]
[mk-app] #2450 + #2473 #2409
[mk-app] #2403 + #2409 #2473
[inst-discovered] theory-solving 0 arith# ; #2403
[mk-app] #2440 = #2403 #2450
[instance] 0 #2440
[attach-enode] #2440 0
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #2403 = #2477 #337
[mk-app] #2440 = #2450 #337
[inst-discovered] theory-solving 0 arith# ; #2440
[mk-app] #2384 = #2440 #2403
[instance] 0 #2384
[attach-enode] #2384 0
[end-of-instance]
[mk-app] #2478 or #2219 #2403
[instance] 0x559938df8db0 ; 3
[attach-enode] #2403 3
[mk-app] #2473 = #337 #2477
[attach-enode] #2473 3
[assign] #2403 justification -1: 78
[end-of-instance]
[mk-app] #2450 or #2481 #2482
[mk-app] #2440 or #2 #2481 #2482
[inst-discovered] theory-solving 0 basic# ; #2440
[mk-app] #2384 = #2440 #2450
[instance] 0 #2384
[attach-enode] #2384 0
[end-of-instance]
[mk-app] #2440 or #2230 #2481 #2482
[instance] 0x559938df8de8 ; 3
[end-of-instance]
[mk-app] #2450 or #2453 #2486
[instance] 0x559938df8e20 ; 3
[attach-enode] #2484 3
[attach-enode] #2486 3
[assign] #2486 justification -1: 262
[end-of-instance]
[mk-app] #2384 or #2283 #2489
[instance] 0x559938df8e58 ; 3
[attach-enode] #2488 3
[attach-enode] #2489 3
[assign] #2489 justification -1: 25
[end-of-instance]
[mk-app] #2373 or #2297 #2499
[instance] 0x559938df8e88 ; 3
[attach-enode] #2495 3
[attach-meaning] #366 arith (- 1)
[mk-app] #2511 * #366 #2406
[mk-app] #2507 + #2405 #2511
[mk-app] #2503 <= #2507 #337
[mk-app] #2504 >= #2507 #337
[attach-enode] #2511 3
[attach-enode] #2507 3
[assign] (not #2498) justification -1: 55
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #2466 + #2399 #2405
[attach-meaning] #366 arith (- 1)
[mk-app] #2466 = #2509 #292
[inst-discovered] theory-solving 0 arith# ; #2506
[mk-app] #2385 = #2506 #2466
[instance] 0 #2385
[attach-enode] #2385 0
[end-of-instance]
[mk-app] #2385 or #2309 #2466
[instance] 0x559938df8eb8 ; 3
[attach-enode] #2466 3
[mk-app] #2374 = #292 #2509
[mk-app] #2368 >= #2509 #292
[attach-enode] #2374 3
[assign] #2466 justification -1: 77
[end-of-instance]
[assign] #2482 clause 453 -458 -379 -390
[assign] #2491 clause 504 509
[assign] #2496 clause 508 509
[assign] #2473 justification -1: 500
[assign] #2374 justification -1: 510
[mk-app] #2519 = #2515 #337
[inst-discovered] theory-solving 0 arith#
[instance] 0 #2519
[end-of-instance]
[new-match] 0x559938e9a7c0 #1191 #1190 #1187 #2407 ; #2484
[assign] #2472 clause 450 -501
[assign] #2367 clause 459 -501
[assign] #2512 clause 456 -511
[assign] #2368 clause 512 -511
[assign] #2480 clause 451 -459 -379 -458 -390
[push] 7
[assign] (not #2417) decision axiom
[assign] #2493 clause 455 454 -456
[assign] #2390 clause 481 454
[assign] #2495 clause 505 -455 -508
[assign] #2503 clause 506 -505
[assign] #2504 clause 507 -505
[mk-app] #2519 = #2507 #337
[inst-discovered] theory-solving 0 arith#
[instance] 0 #2519
[end-of-instance]
[mk-app] #2519 = #2205 #337
[attach-enode] #2519 0
[mk-app] #2520 = #337 #2205
[mk-app] #2521 <= #2205 #337
[attach-enode] #2520 0
[push] 8
[assign] (not #2520) decision axiom
[assign] (not #2521) clause -515 514
[assign] (not #2519) justification -1: -514
[resolve-process] true
[resolve-lit] 0 #2317
[conflict] #2317
[pop] 7 9
[attach-enode] #2376 0
[attach-enode] #2377 0
[attach-enode] #2378 0
[attach-enode] #2379 0
[attach-enode] #2380 0
[attach-enode] #2425 0
[attach-enode] #2426 0
[attach-enode] #2427 0
[attach-enode] #2465 0
[attach-enode] #2458 0
[attach-enode] #2459 0
[attach-enode] #2405 0
[attach-enode] #2406 0
[attach-enode] #2407 0
[attach-enode] #2408 0
[attach-enode] #2409 0
[attach-enode] #2475 0
[attach-enode] #2476 0
[attach-enode] #2477 0
[attach-enode] #2515 0
[attach-enode] #2508 0
[attach-enode] #2509 0
[attach-enode] #2454 0
[attach-meaning] #366 arith (- 1)
[mk-app] #2364 <= #2465 #337
[attach-enode] #2501 0
[mk-app] #2365 <= #2201 #292
[mk-app] #2370 >= #2201 #292
[attach-enode] #2361 0
[attach-enode] #2362 0
[assign] #2362 axiom
[attach-enode] #2392 0
[attach-enode] #2393 0
[assign] #2393 axiom
[assign] #2317 axiom
[assign] (not #2316) clause -409 -410
[assign] (not #2454) clause -460 409
[assign] #2321 justification -1: 465 396
[assign] #2328 justification -1: 466 397
[attach-meaning] #366 arith (- 1)
[mk-app] #2388 + #2193 #2369
[mk-app] #2386 <= #2388 #337
[mk-app] #2387 >= #2388 #337
[attach-enode] #2369 0
[attach-enode] #2388 0
[assign] #2386 justification -1: 396
[assign] #2387 justification -1: 396
[attach-meaning] #366 arith (- 1)
[mk-app] #2428 + #2203 #2399
[mk-app] #2414 <= #2428 #337
[mk-app] #2415 >= #2428 #337
[attach-enode] #2399 0
[attach-enode] #2428 0
[assign] #2414 justification -1: 397
[assign] #2415 justification -1: 397
[assign] #2324 clause 415 -414
[assign] #2331 clause 417 -416
[mk-app] #2464 = #2388 #337
[inst-discovered] theory-solving 0 arith#
[instance] 0 #2464
[end-of-instance]
[mk-app] #2464 = #2428 #337
[inst-discovered] theory-solving 0 arith#
[instance] 0 #2464
[end-of-instance]
[new-match] 0x559938e7dfb0 #1191 #1190 #1213 #2200 ; #2323
[new-match] 0x559938e7dfe8 #1209 #1205 #1212 #2200 ; #2323 (#1213 #1213)
[new-match] 0x559938e7e020 #1191 #1190 #1213 #2204 ; #2330
[new-match] 0x559938e7e058 #1209 #1205 #1212 #2204 ; #2330 (#1213 #1213)
[mk-app] #2464 not #1191
[mk-app] #2514 or #2464 #2372
[instance] 0x559938e7dfb0 ; 2
[attach-enode] #1187 2
[attach-enode] #2371 2
[attach-enode] #2372 2
[assign] #2372 justification -1: 262
[end-of-instance]
[mk-app] #2463 not #1209
[mk-app] #2413 or #2463 #2322 #2382
[instance] 0x559938e7dfe8 ; 2
[mk-app] #2435 = #292 #2381
[mk-app] #2398 = #2380 #2381
[attach-enode] #2381 2
[attach-enode] #2375 2
[mk-app] #2474 = #337 #2281
[attach-enode] #2474 2
[attach-enode] #2435 2
[attach-enode] #2398 2
[attach-enode] #2382 2
[assign] #2382 justification -1: 263 414
[end-of-instance]
[mk-app] #2513 or #2464 #2402
[instance] 0x559938e7e020 ; 2
[attach-enode] #2401 2
[attach-enode] #2402 2
[assign] #2402 justification -1: 262
[end-of-instance]
[mk-app] #2479 or #2463 #2329 #2411
[instance] 0x559938e7e058 ; 2
[mk-app] #2516 = #292 #2410
[mk-app] #2510 = #2409 #2410
[attach-enode] #2410 2
[attach-enode] #2404 2
[mk-app] #2502 = #337 #2285
[attach-enode] #2502 2
[attach-enode] #2516 2
[attach-enode] #2510 2
[attach-enode] #2411 2
[assign] #2411 justification -1: 263 416
[end-of-instance]
[assign] (not #2398) justification -1: -460 415 477
[eq-expl] #1187 root
[new-match] 0x559938df7c60 #1191 #1190 #1187 #2200 ; #2371
[new-match] 0x559938df7c98 #1191 #1190 #1187 #2204 ; #2401
[assign] #2375 clause 472 476
[assign] #2435 clause 475 -472
[assign] #2474 justification -1: 472
[assign] #2501 justification -1: 475 415 477
[assign] #2389 clause 447 -473
[assign] #2359 clause 474 -473
[assign] #2365 clause 463 -462
[assign] #2370 clause 464 -462
[assign] #2224 clause 378 -462
[decide-and-or] #2231 #2227
[push] 2
[assign] (not #2226) decision axiom
[assign] (not #2263) clause -391 379
[mk-app] #2396 = #2271 #2205
[inst-discovered] theory-solving 0 arith#
[instance] 0 #2396
[end-of-instance]
[mk-app] #2396 = #2214 #2208
[inst-discovered] theory-solving 0 arith#
[instance] 0 #2396
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 (not #2370)
[resolve-lit] 0 (not #2365)
[resolve-lit] 0 #2316
[resolve-process] (not #2370)
[resolve-lit] 0 (not #2501)
[resolve-process] (not #2365)
[resolve-process] (not #2501)
[resolve-lit] 0 (not #2435)
[resolve-lit] 0 (not #2324)
[resolve-lit] 0 (not #2382)
[resolve-process] (not #2435)
[resolve-lit] 0 (not #2375)
[resolve-process] (not #2375)
[resolve-lit] 0 #2398
[resolve-process] #2398
[resolve-lit] 0 #2454
[resolve-process] (not #2382)
[resolve-lit] 0 (not #2321)
[resolve-process] (not #2324)
[resolve-lit] 0 (not #1221)
[resolve-process] (not #2321)
[resolve-lit] 0 (not #2362)
[resolve-process] #2454
[resolve-process] #2316
[resolve-lit] 0 (not #2317)
[resolve-process] (not #2317)
[resolve-process] (not #2362)
[conflict] (not #1221)
[pop] 2 3
[attach-enode] #2376 0
[attach-enode] #2377 0
[attach-enode] #2378 0
[attach-enode] #1212 0
[attach-enode] #2379 0
[attach-enode] #2380 0
[attach-enode] #2425 0
[attach-enode] #2426 0
[attach-enode] #2427 0
[attach-enode] #2465 0
[attach-enode] #2458 0
[attach-enode] #2459 0
[attach-enode] #2405 0
[attach-enode] #2406 0
[attach-enode] #2407 0
[attach-enode] #2408 0
[attach-enode] #2409 0
[attach-enode] #2475 0
[attach-enode] #2476 0
[attach-enode] #2477 0
[attach-enode] #2515 0
[attach-enode] #2508 0
[attach-enode] #2509 0
[attach-enode] #2454 0
[attach-meaning] #366 arith (- 1)
[mk-app] #2341 <= #2465 #337
[attach-enode] #2501 0
[mk-app] #2342 <= #2201 #292
[mk-app] #2364 >= #2201 #292
[assign] #2318 axiom
[assign] #2319 axiom
[assign] #2320 axiom
[assign] #2334 axiom
[assign] #2335 axiom
[assign] #2336 axiom
[assign] #2337 axiom
[assign] #2338 axiom
[assign] #2339 axiom
[assign] #2340 axiom
[assign] #2343 axiom
[assign] #2344 axiom
[assign] #2345 axiom
[assign] #2346 axiom
[assign] #2347 axiom
[assign] #2348 axiom
[assign] #2349 axiom
[assign] #2350 axiom
[assign] #2351 axiom
[assign] #2352 axiom
[assign] #2353 axiom
[assign] #2354 axiom
[assign] #2355 axiom
[assign] #2356 axiom
[assign] #2357 axiom
[assign] #2358 axiom
[attach-enode] #2361 0
[attach-enode] #2362 0
[assign] #2362 axiom
[attach-enode] #2392 0
[attach-enode] #2393 0
[assign] #2393 axiom
[assign] #2317 axiom
[assign] (not #1221) axiom
[assign] #1123 clause 256 -433
[assign] #1148 clause 258 -434
[assign] #1210 clause 264 -435
[assign] #1225 clause 267 -436
[assign] #1236 clause 270 -437
[assign] #1255 clause 273 -438
[assign] #1287 clause 278 -439
[assign] #1316 clause 283 -440
[assign] #1352 clause 288 -441
[assign] #1379 clause 293 -442
[assign] #1388 clause 297 -443
[assign] #1397 clause 300 -444
[assign] #1419 clause 303 -445
[assign] #1435 clause 306 -446
[assign] #1471 clause 309 -447
[assign] #1480 clause 312 -448
[assign] #1489 clause 315 -449
[assign] #1503 clause 318 -450
[assign] #1518 clause 321 -451
[assign] #1532 clause 324 -452
[assign] #1546 clause 327 -453
[assign] #1561 clause 330 -454
[assign] #1574 clause 333 -455
[assign] #1590 clause 337 -456
[assign] #1615 clause 340 -457
[assign] #1643 clause 343 -458
[assign] (not #2316) clause -409 -410
[pop] 1 1
[eof]
