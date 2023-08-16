{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

module MAlonzo.Code.SetOmega where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Primitive

-- SetOmega._≡ω_
d__'8801'ω__6 a0 a1 a2 = ()
data T__'8801'ω__6 = C_refl_12
-- SetOmega.congωl
d_congωl_26 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T__'8801'ω__6 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_congωl_26 = erased
-- SetOmega.conglω
d_conglω_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T__'8801'ω__6
d_conglω_42 = erased
-- SetOmega.congωω
d_congωω_56 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T__'8801'ω__6 -> T__'8801'ω__6
d_congωω_56 = erased
-- SetOmega.transω
d_transω_68 ::
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> T__'8801'ω__6 -> T__'8801'ω__6 -> T__'8801'ω__6
d_transω_68 = erased
-- SetOmega.symω
d_symω_76 ::
  () -> AgdaAny -> AgdaAny -> T__'8801'ω__6 -> T__'8801'ω__6
d_symω_76 = erased
-- SetOmega.substω
d_substω_90 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  AgdaAny -> AgdaAny -> T__'8801'ω__6 -> AgdaAny -> AgdaAny
d_substω_90 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_substω_90 v6
du_substω_90 :: AgdaAny -> AgdaAny
du_substω_90 v0 = coe v0
-- SetOmega.substlω
d_substlω_116 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__'8801'ω__6 -> AgdaAny -> AgdaAny
d_substlω_116 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_substlω_116 v11
du_substlω_116 :: AgdaAny -> AgdaAny
du_substlω_116 v0 = coe v0
-- SetOmega.substωl
d_substωl_134 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_substωl_134 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_substωl_134 v6
du_substωl_134 :: AgdaAny -> AgdaAny
du_substωl_134 v0 = coe v0
