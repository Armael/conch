|0100
(100) #03d4
(103) JSR2
(104) #ff0f
(107) DEO
(108) BRK
(109) 0617
(10b) 0617
(10d) ( alloc )
(10d) #010b
(110) LDAk2
(111) ROT2
(112) ADDk2
(113) NIP2
(114) ROT2
(115) STA2
(116) JMPr2
(117) ff
(118) 81
(119) 81
(11a) 81
(11b) 81
(11c) 81
(11d) 81
(11e) ff
(11f) 3c
(120) 4e
(121) 9f
(122) fd
(123) f9
(124) 62
(125) 3c
(126) 00
(127) 3c
(128) 7e
(129) 5a
(12a) 7f
(12b) 1b
(12c) 3c
(12d) 5a
(12e) 18
(12f) 01
(130) 7f
(131) 7b
(132) 73
(133) 63
(134) 43
(135) 7f
(136) ff
(137) 00
(138) 7c
(139) 7c
(13a) 7c
(13b) 7c
(13c) 7c
(13d) 00
(13e) 00
(13f) ( addx8 )
(13f) #0109
(142) LDAk2
(143) #0002
(146) SUB2
(147) SWP2
(148) STA2
(149) #28
(14b) DEI2
(14c) #0109
(14f) LDA2
(150) #0000
(153) ADD2
(154) STA2
(155) #0109
(158) LDA2
(159) #0000
(15c) ADD2
(15d) LDA2
(15e) #0008
(161) ADD2
(162) #28
(164) DEO2
(165) #0109
(168) LDAk2
(169) #0002
(16c) ADD2
(16d) SWP2
(16e) STA2
(16f) JMPr2
(170) ( addy8 )
(170) #0109
(173) LDAk2
(174) #0002
(177) SUB2
(178) SWP2
(179) STA2
(17a) #2a
(17c) DEI2
(17d) #0109
(180) LDA2
(181) #0000
(184) ADD2
(185) STA2
(186) #0109
(189) LDA2
(18a) #0000
(18d) ADD2
(18e) LDA2
(18f) #0008
(192) ADD2
(193) #2a
(195) DEO2
(196) #0109
(199) LDAk2
(19a) #0002
(19d) ADD2
(19e) SWP2
(19f) STA2
(1a0) JMPr2
(1a1) ( draw-one-pixel )
(1a1) #0008
(1a4) #28
(1a6) DEO2
(1a7) #0008
(1aa) #2a
(1ac) DEO2
(1ad) #41
(1af) #2e
(1b1) DEO
(1b2) JMPr2
(1b3) ( draw-a-line )
(1b3) #0109
(1b6) LDAk2
(1b7) #0002
(1ba) SUB2
(1bb) SWP2
(1bc) STA2
(1bd) #0008
(1c0) #0109
(1c3) LDA2
(1c4) #0000
(1c7) ADD2
(1c8) STA2
(1c9) #01f4
(1cc) JMP2
(1cd) #0109
(1d0) LDA2
(1d1) #0000
(1d4) ADD2
(1d5) LDA2
(1d6) #28
(1d8) DEO2
(1d9) #41
(1db) #2e
(1dd) DEO
(1de) #0109
(1e1) LDA2
(1e2) #0000
(1e5) ADD2
(1e6) LDA2
(1e7) #0001
(1ea) ADD2
(1eb) #0109
(1ee) LDA2
(1ef) #0000
(1f2) ADD2
(1f3) STA2
(1f4) #0109
(1f7) LDA2
(1f8) #0000
(1fb) ADD2
(1fc) LDA2
(1fd) #001d
(200) LTH2
(201) #01cd
(204) JCN2
(205) #0109
(208) LDAk2
(209) #0002
(20c) ADD2
(20d) SWP2
(20e) STA2
(20f) JMPr2
(210) ( draw-sprites )
(210) #0008
(213) #28
(215) DEO2
(216) #0008
(219) #2a
(21b) DEO2
(21c) #00
(21e) LDZ2
(21f) #2c
(221) DEO2
(222) #00
(224) #2f
(226) DEO
(227) #013f
(22a) JSR2
(22b) #01
(22d) #2f
(22f) DEO
(230) #013f
(233) JSR2
(234) #02
(236) #2f
(238) DEO
(239) #013f
(23c) JSR2
(23d) #03
(23f) #2f
(241) DEO
(242) #0170
(245) JSR2
(246) #0008
(249) #28
(24b) DEO2
(24c) #04
(24e) #2f
(250) DEO
(251) #013f
(254) JSR2
(255) #05
(257) #2f
(259) DEO
(25a) #013f
(25d) JSR2
(25e) #06
(260) #2f
(262) DEO
(263) #013f
(266) JSR2
(267) #07
(269) #2f
(26b) DEO
(26c) #0170
(26f) JSR2
(270) #0008
(273) #28
(275) DEO2
(276) #08
(278) #2f
(27a) DEO
(27b) #013f
(27e) JSR2
(27f) #09
(281) #2f
(283) DEO
(284) #013f
(287) JSR2
(288) #0a
(28a) #2f
(28c) DEO
(28d) #013f
(290) JSR2
(291) #0b
(293) #2f
(295) DEO
(296) #0170
(299) JSR2
(29a) #0008
(29d) #28
(29f) DEO2
(2a0) #0c
(2a2) #2f
(2a4) DEO
(2a5) #013f
(2a8) JSR2
(2a9) #0d
(2ab) #2f
(2ad) DEO
(2ae) #013f
(2b1) JSR2
(2b2) #0e
(2b4) #2f
(2b6) DEO
(2b7) #013f
(2ba) JSR2
(2bb) #0f
(2bd) #2f
(2bf) DEO
(2c0) JMPr2
(2c1) ( addxc )
(2c1) #0109
(2c4) LDAk2
(2c5) #0002
(2c8) SUB2
(2c9) SWP2
(2ca) STA2
(2cb) #28
(2cd) DEI2
(2ce) #0109
(2d1) LDA2
(2d2) #0000
(2d5) ADD2
(2d6) STA2
(2d7) #0109
(2da) LDA2
(2db) #0000
(2de) ADD2
(2df) LDA2
(2e0) #000c
(2e3) ADD2
(2e4) #28
(2e6) DEO2
(2e7) #0109
(2ea) LDAk2
(2eb) #0002
(2ee) ADD2
(2ef) SWP2
(2f0) STA2
(2f1) JMPr2
(2f2) ( addyc )
(2f2) #0109
(2f5) LDAk2
(2f6) #0002
(2f9) SUB2
(2fa) SWP2
(2fb) STA2
(2fc) #2a
(2fe) DEI2
(2ff) #0109
(302) LDA2
(303) #0000
(306) ADD2
(307) STA2
(308) #0109
(30b) LDA2
(30c) #0000
(30f) ADD2
(310) LDA2
(311) #000c
(314) ADD2
(315) #2a
(317) DEO2
(318) #0109
(31b) LDAk2
(31c) #0002
(31f) ADD2
(320) SWP2
(321) STA2
(322) JMPr2
(323) ( draw-2bpp-sprites )
(323) #0008
(326) #28
(328) DEO2
(329) #0008
(32c) #2a
(32e) DEO2
(32f) #06
(331) LDZ2
(332) #2c
(334) DEO2
(335) #80
(337) #2f
(339) DEO
(33a) #02c1
(33d) JSR2
(33e) #81
(340) #2f
(342) DEO
(343) #02c1
(346) JSR2
(347) #82
(349) #2f
(34b) DEO
(34c) #02c1
(34f) JSR2
(350) #83
(352) #2f
(354) DEO
(355) #02f2
(358) JSR2
(359) #0008
(35c) #28
(35e) DEO2
(35f) #84
(361) #2f
(363) DEO
(364) #02c1
(367) JSR2
(368) #85
(36a) #2f
(36c) DEO
(36d) #02c1
(370) JSR2
(371) #86
(373) #2f
(375) DEO
(376) #02c1
(379) JSR2
(37a) #87
(37c) #2f
(37e) DEO
(37f) #02f2
(382) JSR2
(383) #0008
(386) #28
(388) DEO2
(389) #88
(38b) #2f
(38d) DEO
(38e) #02c1
(391) JSR2
(392) #89
(394) #2f
(396) DEO
(397) #02c1
(39a) JSR2
(39b) #8a
(39d) #2f
(39f) DEO
(3a0) #02c1
(3a3) JSR2
(3a4) #8b
(3a6) #2f
(3a8) DEO
(3a9) #02f2
(3ac) JSR2
(3ad) #0008
(3b0) #28
(3b2) DEO2
(3b3) #8c
(3b5) #2f
(3b7) DEO
(3b8) #02c1
(3bb) JSR2
(3bc) #8d
(3be) #2f
(3c0) DEO
(3c1) #02c1
(3c4) JSR2
(3c5) #8e
(3c7) #2f
(3c9) DEO
(3ca) #02c1
(3cd) JSR2
(3ce) #8f
(3d0) #2f
(3d2) DEO
(3d3) JMPr2
(3d4) ( main )
(3d4) #0109
(3d7) LDAk2
(3d8) #0002
(3db) SUB2
(3dc) SWP2
(3dd) STA2
(3de) #0117
(3e1) #00
(3e3) STZ2
(3e4) #011f
(3e7) #02
(3e9) STZ2
(3ea) #0127
(3ed) #04
(3ef) STZ2
(3f0) #012f
(3f3) #06
(3f5) STZ2
(3f6) #2ce9
(3f9) #08
(3fb) DEO2
(3fc) #01c0
(3ff) #0a
(401) DEO2
(402) #2ce5
(405) #0c
(407) DEO2
(408) #0323
(40b) JSR2
(40c) #0109
(40f) LDAk2
(410) #0002
(413) ADD2
(414) SWP2
(415) STA2
(416) JMPr2

