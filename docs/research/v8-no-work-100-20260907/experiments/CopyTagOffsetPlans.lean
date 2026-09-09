import CopyTagOffsetModel
namespace AspisV8.CopyTagOffset
def plan0 : Plan := (.add (.term 63 ⟨14,by decide⟩) (.term 4 ⟨18,by decide⟩))
theorem count0 : count plan0 ≤ 272 := by decide
theorem value0 (h:Fin 64→Nat) : eval h plan0 = 0 + h 63 * 14 + h 4 * 18 := by
  simp only [plan0,eval]; ring
theorem machine0 (h:Fin 64→Nat) (hh:∀ i,h i<AspisV8.CopyTagSplit.p) : machine h plan0=0 + h 63 * 14 + h 4 * 18 := by
  rw [machine_exact h hh plan0 count0,value0]
#print axioms machine0
def plan1 : Plan := (.term 57 ⟨19,by decide⟩)
theorem count1 : count plan1 ≤ 272 := by decide
theorem value1 (h:Fin 64→Nat) : eval h plan1 = 0 + h 57 * 19 := by
  simp only [plan1,eval]; ring
theorem machine1 (h:Fin 64→Nat) (hh:∀ i,h i<AspisV8.CopyTagSplit.p) : machine h plan1=0 + h 57 * 19 := by
  rw [machine_exact h hh plan1 count1,value1]
#print axioms machine1
def plan2 : Plan := (.add (.add (.term 63 ⟨15,by decide⟩) (.add (.term 57 ⟨65,by decide⟩) (.term 58 ⟨77,by decide⟩))) (.add (.add (.term 59 ⟨89,by decide⟩) (.term 60 ⟨101,by decide⟩)) (.add (.term 61 ⟨113,by decide⟩) (.term 62 ⟨125,by decide⟩))))
theorem count2 : count plan2 ≤ 272 := by decide
theorem value2 (h:Fin 64→Nat) : eval h plan2 = 0 + h 63 * 15 + h 57 * 65 + h 58 * 77 + h 59 * 89 + h 60 * 101 + h 61 * 113 + h 62 * 125 := by
  simp only [plan2,eval]; ring
theorem machine2 (h:Fin 64→Nat) (hh:∀ i,h i<AspisV8.CopyTagSplit.p) : machine h plan2=0 + h 63 * 15 + h 57 * 65 + h 58 * 77 + h 59 * 89 + h 60 * 101 + h 61 * 113 + h 62 * 125 := by
  rw [machine_exact h hh plan2 count2,value2]
#print axioms machine2
def plan3 : Plan := (.term 63 ⟨16,by decide⟩)
theorem count3 : count plan3 ≤ 272 := by decide
theorem value3 (h:Fin 64→Nat) : eval h plan3 = 0 + h 63 * 16 := by
  simp only [plan3,eval]; ring
theorem machine3 (h:Fin 64→Nat) (hh:∀ i,h i<AspisV8.CopyTagSplit.p) : machine h plan3=0 + h 63 * 16 := by
  rw [machine_exact h hh plan3 count3,value3]
#print axioms machine3
def plan4 : Plan := (.add (.add (.term 63 ⟨17,by decide⟩) (.add (.term 57 ⟨68,by decide⟩) (.term 58 ⟨80,by decide⟩))) (.add (.add (.term 59 ⟨92,by decide⟩) (.term 60 ⟨104,by decide⟩)) (.add (.term 61 ⟨116,by decide⟩) (.term 62 ⟨128,by decide⟩))))
theorem count4 : count plan4 ≤ 272 := by decide
theorem value4 (h:Fin 64→Nat) : eval h plan4 = 0 + h 63 * 17 + h 57 * 68 + h 58 * 80 + h 59 * 92 + h 60 * 104 + h 61 * 116 + h 62 * 128 := by
  simp only [plan4,eval]; ring
theorem machine4 (h:Fin 64→Nat) (hh:∀ i,h i<AspisV8.CopyTagSplit.p) : machine h plan4=0 + h 63 * 17 + h 57 * 68 + h 58 * 80 + h 59 * 92 + h 60 * 104 + h 61 * 116 + h 62 * 128 := by
  rw [machine_exact h hh plan4 count4,value4]
#print axioms machine4
def plan5 : Plan := (.add (.add (.term 63 ⟨23,by decide⟩) (.add (.term 57 ⟨71,by decide⟩) (.term 58 ⟨83,by decide⟩))) (.add (.add (.term 59 ⟨95,by decide⟩) (.term 60 ⟨107,by decide⟩)) (.add (.term 61 ⟨119,by decide⟩) (.term 62 ⟨131,by decide⟩))))
theorem count5 : count plan5 ≤ 272 := by decide
theorem value5 (h:Fin 64→Nat) : eval h plan5 = 0 + h 63 * 23 + h 57 * 71 + h 58 * 83 + h 59 * 95 + h 60 * 107 + h 61 * 119 + h 62 * 131 := by
  simp only [plan5,eval]; ring
theorem machine5 (h:Fin 64→Nat) (hh:∀ i,h i<AspisV8.CopyTagSplit.p) : machine h plan5=0 + h 63 * 23 + h 57 * 71 + h 58 * 83 + h 59 * 95 + h 60 * 107 + h 61 * 119 + h 62 * 131 := by
  rw [machine_exact h hh plan5 count5,value5]
#print axioms machine5
def plan6 : Plan := (.add (.add (.add (.add (.add (.term 2 ⟨1,by decide⟩) (.add (.term 25 ⟨2,by decide⟩) (.term 27 ⟨3,by decide⟩))) (.add (.term 28 ⟨4,by decide⟩) (.add (.term 30 ⟨5,by decide⟩) (.term 31 ⟨6,by decide⟩)))) (.add (.add (.term 0 ⟨7,by decide⟩) (.add (.term 32 ⟨20,by decide⟩) (.term 29 ⟨21,by decide⟩))) (.add (.add (.term 33 ⟨24,by decide⟩) (.term 34 ⟨26,by decide⟩)) (.add (.term 35 ⟨28,by decide⟩) (.term 36 ⟨30,by decide⟩))))) (.add (.add (.add (.term 37 ⟨32,by decide⟩) (.add (.term 38 ⟨34,by decide⟩) (.term 39 ⟨36,by decide⟩))) (.add (.term 40 ⟨38,by decide⟩) (.add (.term 41 ⟨40,by decide⟩) (.term 42 ⟨42,by decide⟩)))) (.add (.add (.term 43 ⟨44,by decide⟩) (.add (.term 44 ⟨46,by decide⟩) (.term 45 ⟨48,by decide⟩))) (.add (.add (.term 46 ⟨50,by decide⟩) (.term 47 ⟨52,by decide⟩)) (.add (.term 48 ⟨54,by decide⟩) (.term 49 ⟨56,by decide⟩)))))) (.add (.add (.add (.add (.term 50 ⟨58,by decide⟩) (.add (.term 51 ⟨60,by decide⟩) (.term 52 ⟨62,by decide⟩))) (.add (.term 3 ⟨64,by decide⟩) (.add (.term 4 ⟨67,by decide⟩) (.term 5 ⟨70,by decide⟩)))) (.add (.add (.term 6 ⟨73,by decide⟩) (.add (.term 7 ⟨76,by decide⟩) (.term 8 ⟨79,by decide⟩))) (.add (.add (.term 9 ⟨82,by decide⟩) (.term 10 ⟨85,by decide⟩)) (.add (.term 11 ⟨88,by decide⟩) (.term 12 ⟨91,by decide⟩))))) (.add (.add (.add (.term 13 ⟨94,by decide⟩) (.add (.term 14 ⟨97,by decide⟩) (.term 15 ⟨100,by decide⟩))) (.add (.add (.term 16 ⟨103,by decide⟩) (.term 17 ⟨106,by decide⟩)) (.add (.term 18 ⟨109,by decide⟩) (.term 19 ⟨112,by decide⟩)))) (.add (.add (.term 20 ⟨115,by decide⟩) (.add (.term 21 ⟨118,by decide⟩) (.term 22 ⟨121,by decide⟩))) (.add (.add (.term 23 ⟨124,by decide⟩) (.term 24 ⟨127,by decide⟩)) (.add (.term 54 ⟨130,by decide⟩) (.term 55 ⟨133,by decide⟩)))))))
theorem count6 : count plan6 ≤ 272 := by decide
theorem value6 (h:Fin 64→Nat) : eval h plan6 = 0 + h 1 * 0 + h 2 * 1 + h 25 * 2 + h 27 * 3 + h 28 * 4 + h 30 * 5 + h 31 * 6 + h 0 * 7 + h 32 * 20 + h 29 * 21 + h 33 * 24 + h 34 * 26 + h 35 * 28 + h 36 * 30 + h 37 * 32 + h 38 * 34 + h 39 * 36 + h 40 * 38 + h 41 * 40 + h 42 * 42 + h 43 * 44 + h 44 * 46 + h 45 * 48 + h 46 * 50 + h 47 * 52 + h 48 * 54 + h 49 * 56 + h 50 * 58 + h 51 * 60 + h 52 * 62 + h 3 * 64 + h 4 * 67 + h 5 * 70 + h 6 * 73 + h 7 * 76 + h 8 * 79 + h 9 * 82 + h 10 * 85 + h 11 * 88 + h 12 * 91 + h 13 * 94 + h 14 * 97 + h 15 * 100 + h 16 * 103 + h 17 * 106 + h 18 * 109 + h 19 * 112 + h 20 * 115 + h 21 * 118 + h 22 * 121 + h 23 * 124 + h 24 * 127 + h 54 * 130 + h 55 * 133 := by
  simp only [plan6,eval]; ring
theorem machine6 (h:Fin 64→Nat) (hh:∀ i,h i<AspisV8.CopyTagSplit.p) : machine h plan6=0 + h 1 * 0 + h 2 * 1 + h 25 * 2 + h 27 * 3 + h 28 * 4 + h 30 * 5 + h 31 * 6 + h 0 * 7 + h 32 * 20 + h 29 * 21 + h 33 * 24 + h 34 * 26 + h 35 * 28 + h 36 * 30 + h 37 * 32 + h 38 * 34 + h 39 * 36 + h 40 * 38 + h 41 * 40 + h 42 * 42 + h 43 * 44 + h 44 * 46 + h 45 * 48 + h 46 * 50 + h 47 * 52 + h 48 * 54 + h 49 * 56 + h 50 * 58 + h 51 * 60 + h 52 * 62 + h 3 * 64 + h 4 * 67 + h 5 * 70 + h 6 * 73 + h 7 * 76 + h 8 * 79 + h 9 * 82 + h 10 * 85 + h 11 * 88 + h 12 * 91 + h 13 * 94 + h 14 * 97 + h 15 * 100 + h 16 * 103 + h 17 * 106 + h 18 * 109 + h 19 * 112 + h 20 * 115 + h 21 * 118 + h 22 * 121 + h 23 * 124 + h 24 * 127 + h 54 * 130 + h 55 * 133 := by
  rw [machine_exact h hh plan6 count6,value6]
#print axioms machine6
def plan7 : Plan := (.add (.add (.term 0 ⟨8,by decide⟩) (.term 2 ⟨9,by decide⟩)) (.add (.term 3 ⟨10,by decide⟩) (.add (.term 28 ⟨12,by decide⟩) (.term 31 ⟨13,by decide⟩))))
theorem count7 : count plan7 ≤ 272 := by decide
theorem value7 (h:Fin 64→Nat) : eval h plan7 = 0 + h 0 * 8 + h 2 * 9 + h 3 * 10 + h 28 * 12 + h 31 * 13 := by
  simp only [plan7,eval]; ring
theorem machine7 (h:Fin 64→Nat) (hh:∀ i,h i<AspisV8.CopyTagSplit.p) : machine h plan7=0 + h 0 * 8 + h 2 * 9 + h 3 * 10 + h 28 * 12 + h 31 * 13 := by
  rw [machine_exact h hh plan7 count7,value7]
#print axioms machine7
def plan8 : Plan := (.add (.add (.term 57 ⟨74,by decide⟩) (.add (.term 58 ⟨86,by decide⟩) (.term 59 ⟨98,by decide⟩))) (.add (.term 60 ⟨110,by decide⟩) (.add (.term 61 ⟨122,by decide⟩) (.term 62 ⟨134,by decide⟩))))
theorem count8 : count plan8 ≤ 272 := by decide
theorem value8 (h:Fin 64→Nat) : eval h plan8 = 0 + h 57 * 74 + h 58 * 86 + h 59 * 98 + h 60 * 110 + h 61 * 122 + h 62 * 134 := by
  simp only [plan8,eval]; ring
theorem machine8 (h:Fin 64→Nat) (hh:∀ i,h i<AspisV8.CopyTagSplit.p) : machine h plan8=0 + h 57 * 74 + h 58 * 86 + h 59 * 98 + h 60 * 110 + h 61 * 122 + h 62 * 134 := by
  rw [machine_exact h hh plan8 count8,value8]
#print axioms machine8
def plan9 : Plan := (.add (.add (.term 57 ⟨66,by decide⟩) (.add (.term 58 ⟨78,by decide⟩) (.term 59 ⟨90,by decide⟩))) (.add (.term 60 ⟨102,by decide⟩) (.add (.term 61 ⟨114,by decide⟩) (.term 62 ⟨126,by decide⟩))))
theorem count9 : count plan9 ≤ 272 := by decide
theorem value9 (h:Fin 64→Nat) : eval h plan9 = 0 + h 57 * 66 + h 58 * 78 + h 59 * 90 + h 60 * 102 + h 61 * 114 + h 62 * 126 := by
  simp only [plan9,eval]; ring
theorem machine9 (h:Fin 64→Nat) (hh:∀ i,h i<AspisV8.CopyTagSplit.p) : machine h plan9=0 + h 57 * 66 + h 58 * 78 + h 59 * 90 + h 60 * 102 + h 61 * 114 + h 62 * 126 := by
  rw [machine_exact h hh plan9 count9,value9]
#print axioms machine9
def plan10 : Plan := (.add (.add (.term 57 ⟨69,by decide⟩) (.add (.term 58 ⟨81,by decide⟩) (.term 59 ⟨93,by decide⟩))) (.add (.term 60 ⟨105,by decide⟩) (.add (.term 61 ⟨117,by decide⟩) (.term 62 ⟨129,by decide⟩))))
theorem count10 : count plan10 ≤ 272 := by decide
theorem value10 (h:Fin 64→Nat) : eval h plan10 = 0 + h 57 * 69 + h 58 * 81 + h 59 * 93 + h 60 * 105 + h 61 * 117 + h 62 * 129 := by
  simp only [plan10,eval]; ring
theorem machine10 (h:Fin 64→Nat) (hh:∀ i,h i<AspisV8.CopyTagSplit.p) : machine h plan10=0 + h 57 * 69 + h 58 * 81 + h 59 * 93 + h 60 * 105 + h 61 * 117 + h 62 * 129 := by
  rw [machine_exact h hh plan10 count10,value10]
#print axioms machine10
def plan11 : Plan := (.add (.add (.term 57 ⟨72,by decide⟩) (.add (.term 58 ⟨84,by decide⟩) (.term 59 ⟨96,by decide⟩))) (.add (.term 60 ⟨108,by decide⟩) (.add (.term 61 ⟨120,by decide⟩) (.term 62 ⟨132,by decide⟩))))
theorem count11 : count plan11 ≤ 272 := by decide
theorem value11 (h:Fin 64→Nat) : eval h plan11 = 0 + h 57 * 72 + h 58 * 84 + h 59 * 96 + h 60 * 108 + h 61 * 120 + h 62 * 132 := by
  simp only [plan11,eval]; ring
theorem machine11 (h:Fin 64→Nat) (hh:∀ i,h i<AspisV8.CopyTagSplit.p) : machine h plan11=0 + h 57 * 72 + h 58 * 84 + h 59 * 96 + h 60 * 108 + h 61 * 120 + h 62 * 132 := by
  rw [machine_exact h hh plan11 count11,value11]
#print axioms machine11
def plan12 : Plan := (.add (.add (.add (.add (.term 32 ⟨22,by decide⟩) (.term 33 ⟨25,by decide⟩)) (.add (.term 34 ⟨27,by decide⟩) (.add (.term 35 ⟨29,by decide⟩) (.term 36 ⟨31,by decide⟩)))) (.add (.add (.term 37 ⟨33,by decide⟩) (.term 38 ⟨35,by decide⟩)) (.add (.term 39 ⟨37,by decide⟩) (.add (.term 40 ⟨39,by decide⟩) (.term 41 ⟨41,by decide⟩))))) (.add (.add (.add (.term 42 ⟨43,by decide⟩) (.term 43 ⟨45,by decide⟩)) (.add (.term 44 ⟨47,by decide⟩) (.add (.term 45 ⟨49,by decide⟩) (.term 46 ⟨51,by decide⟩)))) (.add (.add (.term 47 ⟨53,by decide⟩) (.add (.term 48 ⟨55,by decide⟩) (.term 49 ⟨57,by decide⟩))) (.add (.term 50 ⟨59,by decide⟩) (.add (.term 51 ⟨61,by decide⟩) (.term 52 ⟨63,by decide⟩))))))
theorem count12 : count plan12 ≤ 272 := by decide
theorem value12 (h:Fin 64→Nat) : eval h plan12 = 0 + h 32 * 22 + h 33 * 25 + h 34 * 27 + h 35 * 29 + h 36 * 31 + h 37 * 33 + h 38 * 35 + h 39 * 37 + h 40 * 39 + h 41 * 41 + h 42 * 43 + h 43 * 45 + h 44 * 47 + h 45 * 49 + h 46 * 51 + h 47 * 53 + h 48 * 55 + h 49 * 57 + h 50 * 59 + h 51 * 61 + h 52 * 63 := by
  simp only [plan12,eval]; ring
theorem machine12 (h:Fin 64→Nat) (hh:∀ i,h i<AspisV8.CopyTagSplit.p) : machine h plan12=0 + h 32 * 22 + h 33 * 25 + h 34 * 27 + h 35 * 29 + h 36 * 31 + h 37 * 33 + h 38 * 35 + h 39 * 37 + h 40 * 39 + h 41 * 41 + h 42 * 43 + h 43 * 45 + h 44 * 47 + h 45 * 49 + h 46 * 51 + h 47 * 53 + h 48 * 55 + h 49 * 57 + h 50 * 59 + h 51 * 61 + h 52 * 63 := by
  rw [machine_exact h hh plan12 count12,value12]
#print axioms machine12
def plan13 : Plan := (.term 2 ⟨11,by decide⟩)
theorem count13 : count plan13 ≤ 272 := by decide
theorem value13 (h:Fin 64→Nat) : eval h plan13 = 0 + h 2 * 11 := by
  simp only [plan13,eval]; ring
theorem machine13 (h:Fin 64→Nat) (hh:∀ i,h i<AspisV8.CopyTagSplit.p) : machine h plan13=0 + h 2 * 11 := by
  rw [machine_exact h hh plan13 count13,value13]
#print axioms machine13
def plan14 : Plan := (.add (.add (.term 57 ⟨75,by decide⟩) (.add (.term 58 ⟨87,by decide⟩) (.term 59 ⟨99,by decide⟩))) (.add (.term 60 ⟨111,by decide⟩) (.add (.term 61 ⟨123,by decide⟩) (.term 62 ⟨135,by decide⟩))))
theorem count14 : count plan14 ≤ 272 := by decide
theorem value14 (h:Fin 64→Nat) : eval h plan14 = 0 + h 57 * 75 + h 58 * 87 + h 59 * 99 + h 60 * 111 + h 61 * 123 + h 62 * 135 := by
  simp only [plan14,eval]; ring
theorem machine14 (h:Fin 64→Nat) (hh:∀ i,h i<AspisV8.CopyTagSplit.p) : machine h plan14=0 + h 57 * 75 + h 58 * 87 + h 59 * 99 + h 60 * 111 + h 61 * 123 + h 62 * 135 := by
  rw [machine_exact h hh plan14 count14,value14]
#print axioms machine14
def plan15 : Plan := (.add (.add (.add (.add (.add (.term 3 ⟨1,by decide⟩) (.add (.term 26 ⟨2,by decide⟩) (.term 28 ⟨3,by decide⟩))) (.add (.term 29 ⟨4,by decide⟩) (.add (.term 31 ⟨5,by decide⟩) (.term 32 ⟨6,by decide⟩)))) (.add (.add (.term 63 ⟨11,by decide⟩) (.add (.term 33 ⟨23,by decide⟩) (.term 34 ⟨25,by decide⟩))) (.add (.add (.term 35 ⟨27,by decide⟩) (.term 36 ⟨29,by decide⟩)) (.add (.term 37 ⟨31,by decide⟩) (.term 38 ⟨33,by decide⟩))))) (.add (.add (.add (.term 39 ⟨35,by decide⟩) (.add (.term 40 ⟨37,by decide⟩) (.term 41 ⟨39,by decide⟩))) (.add (.term 42 ⟨41,by decide⟩) (.add (.term 43 ⟨43,by decide⟩) (.term 44 ⟨45,by decide⟩)))) (.add (.add (.term 45 ⟨47,by decide⟩) (.add (.term 46 ⟨49,by decide⟩) (.term 47 ⟨51,by decide⟩))) (.add (.add (.term 48 ⟨53,by decide⟩) (.term 49 ⟨55,by decide⟩)) (.add (.term 50 ⟨57,by decide⟩) (.term 51 ⟨59,by decide⟩)))))) (.add (.add (.add (.add (.term 52 ⟨61,by decide⟩) (.add (.term 53 ⟨63,by decide⟩) (.term 4 ⟨66,by decide⟩))) (.add (.term 5 ⟨69,by decide⟩) (.add (.term 6 ⟨72,by decide⟩) (.term 7 ⟨75,by decide⟩)))) (.add (.add (.term 8 ⟨78,by decide⟩) (.add (.term 9 ⟨81,by decide⟩) (.term 10 ⟨84,by decide⟩))) (.add (.add (.term 11 ⟨87,by decide⟩) (.term 12 ⟨90,by decide⟩)) (.add (.term 13 ⟨93,by decide⟩) (.term 14 ⟨96,by decide⟩))))) (.add (.add (.add (.term 15 ⟨99,by decide⟩) (.add (.term 16 ⟨102,by decide⟩) (.term 17 ⟨105,by decide⟩))) (.add (.term 18 ⟨108,by decide⟩) (.add (.term 19 ⟨111,by decide⟩) (.term 20 ⟨114,by decide⟩)))) (.add (.add (.term 21 ⟨117,by decide⟩) (.add (.term 22 ⟨120,by decide⟩) (.term 23 ⟨123,by decide⟩))) (.add (.add (.term 24 ⟨126,by decide⟩) (.term 54 ⟨129,by decide⟩)) (.add (.term 55 ⟨132,by decide⟩) (.term 56 ⟨135,by decide⟩)))))))
theorem count15 : count plan15 ≤ 272 := by decide
theorem value15 (h:Fin 64→Nat) : eval h plan15 = 0 + h 2 * 0 + h 3 * 1 + h 26 * 2 + h 28 * 3 + h 29 * 4 + h 31 * 5 + h 32 * 6 + h 63 * 11 + h 33 * 23 + h 34 * 25 + h 35 * 27 + h 36 * 29 + h 37 * 31 + h 38 * 33 + h 39 * 35 + h 40 * 37 + h 41 * 39 + h 42 * 41 + h 43 * 43 + h 44 * 45 + h 45 * 47 + h 46 * 49 + h 47 * 51 + h 48 * 53 + h 49 * 55 + h 50 * 57 + h 51 * 59 + h 52 * 61 + h 53 * 63 + h 4 * 66 + h 5 * 69 + h 6 * 72 + h 7 * 75 + h 8 * 78 + h 9 * 81 + h 10 * 84 + h 11 * 87 + h 12 * 90 + h 13 * 93 + h 14 * 96 + h 15 * 99 + h 16 * 102 + h 17 * 105 + h 18 * 108 + h 19 * 111 + h 20 * 114 + h 21 * 117 + h 22 * 120 + h 23 * 123 + h 24 * 126 + h 54 * 129 + h 55 * 132 + h 56 * 135 := by
  simp only [plan15,eval]; ring
theorem machine15 (h:Fin 64→Nat) (hh:∀ i,h i<AspisV8.CopyTagSplit.p) : machine h plan15=0 + h 2 * 0 + h 3 * 1 + h 26 * 2 + h 28 * 3 + h 29 * 4 + h 31 * 5 + h 32 * 6 + h 63 * 11 + h 33 * 23 + h 34 * 25 + h 35 * 27 + h 36 * 29 + h 37 * 31 + h 38 * 33 + h 39 * 35 + h 40 * 37 + h 41 * 39 + h 42 * 41 + h 43 * 43 + h 44 * 45 + h 45 * 47 + h 46 * 49 + h 47 * 51 + h 48 * 53 + h 49 * 55 + h 50 * 57 + h 51 * 59 + h 52 * 61 + h 53 * 63 + h 4 * 66 + h 5 * 69 + h 6 * 72 + h 7 * 75 + h 8 * 78 + h 9 * 81 + h 10 * 84 + h 11 * 87 + h 12 * 90 + h 13 * 93 + h 14 * 96 + h 15 * 99 + h 16 * 102 + h 17 * 105 + h 18 * 108 + h 19 * 111 + h 20 * 114 + h 21 * 117 + h 22 * 120 + h 23 * 123 + h 24 * 126 + h 54 * 129 + h 55 * 132 + h 56 * 135 := by
  rw [machine_exact h hh plan15 count15,value15]
#print axioms machine15
def plan16 : Plan := (.add (.add (.term 57 ⟨64,by decide⟩) (.add (.term 58 ⟨76,by decide⟩) (.term 59 ⟨88,by decide⟩))) (.add (.term 60 ⟨100,by decide⟩) (.add (.term 61 ⟨112,by decide⟩) (.term 62 ⟨124,by decide⟩))))
theorem count16 : count plan16 ≤ 272 := by decide
theorem value16 (h:Fin 64→Nat) : eval h plan16 = 0 + h 57 * 64 + h 58 * 76 + h 59 * 88 + h 60 * 100 + h 61 * 112 + h 62 * 124 := by
  simp only [plan16,eval]; ring
theorem machine16 (h:Fin 64→Nat) (hh:∀ i,h i<AspisV8.CopyTagSplit.p) : machine h plan16=0 + h 57 * 64 + h 58 * 76 + h 59 * 88 + h 60 * 100 + h 61 * 112 + h 62 * 124 := by
  rw [machine_exact h hh plan16 count16,value16]
#print axioms machine16
def plan17 : Plan := (.term 63 ⟨12,by decide⟩)
theorem count17 : count plan17 ≤ 272 := by decide
theorem value17 (h:Fin 64→Nat) : eval h plan17 = 0 + h 63 * 12 := by
  simp only [plan17,eval]; ring
theorem machine17 (h:Fin 64→Nat) (hh:∀ i,h i<AspisV8.CopyTagSplit.p) : machine h plan17=0 + h 63 * 12 := by
  rw [machine_exact h hh plan17 count17,value17]
#print axioms machine17
def plan18 : Plan := (.term 63 ⟨13,by decide⟩)
theorem count18 : count plan18 ≤ 272 := by decide
theorem value18 (h:Fin 64→Nat) : eval h plan18 = 0 + h 63 * 13 := by
  simp only [plan18,eval]; ring
theorem machine18 (h:Fin 64→Nat) (hh:∀ i,h i<AspisV8.CopyTagSplit.p) : machine h plan18=0 + h 63 * 13 := by
  rw [machine_exact h hh plan18 count18,value18]
#print axioms machine18
def plan19 : Plan := (.add (.add (.term 57 ⟨67,by decide⟩) (.add (.term 58 ⟨79,by decide⟩) (.term 59 ⟨91,by decide⟩))) (.add (.term 60 ⟨103,by decide⟩) (.add (.term 61 ⟨115,by decide⟩) (.term 62 ⟨127,by decide⟩))))
theorem count19 : count plan19 ≤ 272 := by decide
theorem value19 (h:Fin 64→Nat) : eval h plan19 = 0 + h 57 * 67 + h 58 * 79 + h 59 * 91 + h 60 * 103 + h 61 * 115 + h 62 * 127 := by
  simp only [plan19,eval]; ring
theorem machine19 (h:Fin 64→Nat) (hh:∀ i,h i<AspisV8.CopyTagSplit.p) : machine h plan19=0 + h 57 * 67 + h 58 * 79 + h 59 * 91 + h 60 * 103 + h 61 * 115 + h 62 * 127 := by
  rw [machine_exact h hh plan19 count19,value19]
#print axioms machine19
def plan20 : Plan := (.term 63 ⟨14,by decide⟩)
theorem count20 : count plan20 ≤ 272 := by decide
theorem value20 (h:Fin 64→Nat) : eval h plan20 = 0 + h 63 * 14 := by
  simp only [plan20,eval]; ring
theorem machine20 (h:Fin 64→Nat) (hh:∀ i,h i<AspisV8.CopyTagSplit.p) : machine h plan20=0 + h 63 * 14 := by
  rw [machine_exact h hh plan20 count20,value20]
#print axioms machine20
def plan21 : Plan := (.term 63 ⟨16,by decide⟩)
theorem count21 : count plan21 ≤ 272 := by decide
theorem value21 (h:Fin 64→Nat) : eval h plan21 = 0 + h 63 * 16 := by
  simp only [plan21,eval]; ring
theorem machine21 (h:Fin 64→Nat) (hh:∀ i,h i<AspisV8.CopyTagSplit.p) : machine h plan21=0 + h 63 * 16 := by
  rw [machine_exact h hh plan21 count21,value21]
#print axioms machine21
def plan22 : Plan := (.add (.add (.term 63 ⟨18,by decide⟩) (.add (.term 57 ⟨70,by decide⟩) (.term 58 ⟨82,by decide⟩))) (.add (.add (.term 59 ⟨94,by decide⟩) (.term 60 ⟨106,by decide⟩)) (.add (.term 61 ⟨118,by decide⟩) (.term 62 ⟨130,by decide⟩))))
theorem count22 : count plan22 ≤ 272 := by decide
theorem value22 (h:Fin 64→Nat) : eval h plan22 = 0 + h 63 * 18 + h 57 * 70 + h 58 * 82 + h 59 * 94 + h 60 * 106 + h 61 * 118 + h 62 * 130 := by
  simp only [plan22,eval]; ring
theorem machine22 (h:Fin 64→Nat) (hh:∀ i,h i<AspisV8.CopyTagSplit.p) : machine h plan22=0 + h 63 * 18 + h 57 * 70 + h 58 * 82 + h 59 * 94 + h 60 * 106 + h 61 * 118 + h 62 * 130 := by
  rw [machine_exact h hh plan22 count22,value22]
#print axioms machine22
def plan23 : Plan := (.term 63 ⟨20,by decide⟩)
theorem count23 : count plan23 ≤ 272 := by decide
theorem value23 (h:Fin 64→Nat) : eval h plan23 = 0 + h 63 * 20 := by
  simp only [plan23,eval]; ring
theorem machine23 (h:Fin 64→Nat) (hh:∀ i,h i<AspisV8.CopyTagSplit.p) : machine h plan23=0 + h 63 * 20 := by
  rw [machine_exact h hh plan23 count23,value23]
#print axioms machine23
def plan24 : Plan := (.add (.add (.add (.add (.add (.term 1 ⟨7,by decide⟩) (.add (.term 25 ⟨8,by decide⟩) (.term 26 ⟨9,by decide⟩))) (.add (.term 33 ⟨21,by decide⟩) (.add (.term 34 ⟨24,by decide⟩) (.term 35 ⟨26,by decide⟩)))) (.add (.add (.term 36 ⟨28,by decide⟩) (.add (.term 37 ⟨30,by decide⟩) (.term 38 ⟨32,by decide⟩))) (.add (.term 39 ⟨34,by decide⟩) (.add (.term 40 ⟨36,by decide⟩) (.term 41 ⟨38,by decide⟩))))) (.add (.add (.add (.term 42 ⟨40,by decide⟩) (.add (.term 43 ⟨42,by decide⟩) (.term 44 ⟨44,by decide⟩))) (.add (.term 45 ⟨46,by decide⟩) (.add (.term 46 ⟨48,by decide⟩) (.term 47 ⟨50,by decide⟩)))) (.add (.add (.term 48 ⟨52,by decide⟩) (.add (.term 49 ⟨54,by decide⟩) (.term 50 ⟨56,by decide⟩))) (.add (.term 51 ⟨58,by decide⟩) (.add (.term 52 ⟨60,by decide⟩) (.term 53 ⟨62,by decide⟩)))))) (.add (.add (.add (.add (.term 4 ⟨65,by decide⟩) (.add (.term 5 ⟨68,by decide⟩) (.term 6 ⟨71,by decide⟩))) (.add (.term 7 ⟨74,by decide⟩) (.add (.term 8 ⟨77,by decide⟩) (.term 9 ⟨80,by decide⟩)))) (.add (.add (.term 10 ⟨83,by decide⟩) (.add (.term 11 ⟨86,by decide⟩) (.term 12 ⟨89,by decide⟩))) (.add (.term 13 ⟨92,by decide⟩) (.add (.term 14 ⟨95,by decide⟩) (.term 15 ⟨98,by decide⟩))))) (.add (.add (.add (.term 16 ⟨101,by decide⟩) (.add (.term 17 ⟨104,by decide⟩) (.term 18 ⟨107,by decide⟩))) (.add (.term 19 ⟨110,by decide⟩) (.add (.term 20 ⟨113,by decide⟩) (.term 21 ⟨116,by decide⟩)))) (.add (.add (.term 22 ⟨119,by decide⟩) (.add (.term 23 ⟨122,by decide⟩) (.term 24 ⟨125,by decide⟩))) (.add (.term 54 ⟨128,by decide⟩) (.add (.term 55 ⟨131,by decide⟩) (.term 56 ⟨134,by decide⟩)))))))
theorem count24 : count plan24 ≤ 272 := by decide
theorem value24 (h:Fin 64→Nat) : eval h plan24 = 0 + h 1 * 7 + h 25 * 8 + h 26 * 9 + h 33 * 21 + h 34 * 24 + h 35 * 26 + h 36 * 28 + h 37 * 30 + h 38 * 32 + h 39 * 34 + h 40 * 36 + h 41 * 38 + h 42 * 40 + h 43 * 42 + h 44 * 44 + h 45 * 46 + h 46 * 48 + h 47 * 50 + h 48 * 52 + h 49 * 54 + h 50 * 56 + h 51 * 58 + h 52 * 60 + h 53 * 62 + h 4 * 65 + h 5 * 68 + h 6 * 71 + h 7 * 74 + h 8 * 77 + h 9 * 80 + h 10 * 83 + h 11 * 86 + h 12 * 89 + h 13 * 92 + h 14 * 95 + h 15 * 98 + h 16 * 101 + h 17 * 104 + h 18 * 107 + h 19 * 110 + h 20 * 113 + h 21 * 116 + h 22 * 119 + h 23 * 122 + h 24 * 125 + h 54 * 128 + h 55 * 131 + h 56 * 134 := by
  simp only [plan24,eval]; ring
theorem machine24 (h:Fin 64→Nat) (hh:∀ i,h i<AspisV8.CopyTagSplit.p) : machine h plan24=0 + h 1 * 7 + h 25 * 8 + h 26 * 9 + h 33 * 21 + h 34 * 24 + h 35 * 26 + h 36 * 28 + h 37 * 30 + h 38 * 32 + h 39 * 34 + h 40 * 36 + h 41 * 38 + h 42 * 40 + h 43 * 42 + h 44 * 44 + h 45 * 46 + h 46 * 48 + h 47 * 50 + h 48 * 52 + h 49 * 54 + h 50 * 56 + h 51 * 58 + h 52 * 60 + h 53 * 62 + h 4 * 65 + h 5 * 68 + h 6 * 71 + h 7 * 74 + h 8 * 77 + h 9 * 80 + h 10 * 83 + h 11 * 86 + h 12 * 89 + h 13 * 92 + h 14 * 95 + h 15 * 98 + h 16 * 101 + h 17 * 104 + h 18 * 107 + h 19 * 110 + h 20 * 113 + h 21 * 116 + h 22 * 119 + h 23 * 122 + h 24 * 125 + h 54 * 128 + h 55 * 131 + h 56 * 134 := by
  rw [machine_exact h hh plan24 count24,value24]
#print axioms machine24
def plan25 : Plan := (.add (.add (.term 57 ⟨73,by decide⟩) (.add (.term 58 ⟨85,by decide⟩) (.term 59 ⟨97,by decide⟩))) (.add (.term 60 ⟨109,by decide⟩) (.add (.term 61 ⟨121,by decide⟩) (.term 62 ⟨133,by decide⟩))))
theorem count25 : count plan25 ≤ 272 := by decide
theorem value25 (h:Fin 64→Nat) : eval h plan25 = 0 + h 57 * 73 + h 58 * 85 + h 59 * 97 + h 60 * 109 + h 61 * 121 + h 62 * 133 := by
  simp only [plan25,eval]; ring
theorem machine25 (h:Fin 64→Nat) (hh:∀ i,h i<AspisV8.CopyTagSplit.p) : machine h plan25=0 + h 57 * 73 + h 58 * 85 + h 59 * 97 + h 60 * 109 + h 61 * 121 + h 62 * 133 := by
  rw [machine_exact h hh plan25 count25,value25]
#print axioms machine25
def plan26 : Plan := (.term 63 ⟨15,by decide⟩)
theorem count26 : count plan26 ≤ 272 := by decide
theorem value26 (h:Fin 64→Nat) : eval h plan26 = 0 + h 63 * 15 := by
  simp only [plan26,eval]; ring
theorem machine26 (h:Fin 64→Nat) (hh:∀ i,h i<AspisV8.CopyTagSplit.p) : machine h plan26=0 + h 63 * 15 := by
  rw [machine_exact h hh plan26 count26,value26]
#print axioms machine26
def plan27 : Plan := (.term 63 ⟨17,by decide⟩)
theorem count27 : count plan27 ≤ 272 := by decide
theorem value27 (h:Fin 64→Nat) : eval h plan27 = 0 + h 63 * 17 := by
  simp only [plan27,eval]; ring
theorem machine27 (h:Fin 64→Nat) (hh:∀ i,h i<AspisV8.CopyTagSplit.p) : machine h plan27=0 + h 63 * 17 := by
  rw [machine_exact h hh plan27 count27,value27]
#print axioms machine27
def plan28 : Plan := (.term 63 ⟨19,by decide⟩)
theorem count28 : count plan28 ≤ 272 := by decide
theorem value28 (h:Fin 64→Nat) : eval h plan28 = 0 + h 63 * 19 := by
  simp only [plan28,eval]; ring
theorem machine28 (h:Fin 64→Nat) (hh:∀ i,h i<AspisV8.CopyTagSplit.p) : machine h plan28=0 + h 63 * 19 := by
  rw [machine_exact h hh plan28 count28,value28]
#print axioms machine28
def plan29 : Plan := (.add (.term 26 ⟨10,by decide⟩) (.term 33 ⟨22,by decide⟩))
theorem count29 : count plan29 ≤ 272 := by decide
theorem value29 (h:Fin 64→Nat) : eval h plan29 = 0 + h 26 * 10 + h 33 * 22 := by
  simp only [plan29,eval]; ring
theorem machine29 (h:Fin 64→Nat) (hh:∀ i,h i<AspisV8.CopyTagSplit.p) : machine h plan29=0 + h 26 * 10 + h 33 * 22 := by
  rw [machine_exact h hh plan29 count29,value29]
#print axioms machine29
def select0 : Fin 15→Plan := ![plan0,plan1,plan2,plan3,plan4,plan5,plan6,plan7,plan8,plan9,plan10,plan11,plan12,plan13,plan14]
def select15 : Fin 15→Plan := ![plan15,plan16,plan17,plan18,plan19,plan20,plan21,plan22,plan23,plan24,plan25,plan26,plan27,plan28,plan29]
def select (i:Fin 30) : Plan :=
  if hh:i.val<15 then select0 ⟨i.val,hh⟩ else select15 ⟨i.val-15,by omega⟩
theorem every_selected_plan_count (i:Fin 30) : count (select i)≤272 := by
  fin_cases i
  · exact count0
  · exact count1
  · exact count2
  · exact count3
  · exact count4
  · exact count5
  · exact count6
  · exact count7
  · exact count8
  · exact count9
  · exact count10
  · exact count11
  · exact count12
  · exact count13
  · exact count14
  · exact count15
  · exact count16
  · exact count17
  · exact count18
  · exact count19
  · exact count20
  · exact count21
  · exact count22
  · exact count23
  · exact count24
  · exact count25
  · exact count26
  · exact count27
  · exact count28
  · exact count29
theorem every_machine_exact (i:Fin 30) (h:Fin 64→Nat) (hh:∀ j,h j<AspisV8.CopyTagSplit.p) :
    machine h (select i)=eval h (select i) := machine_exact h hh (select i) (every_selected_plan_count i)
#print axioms every_selected_plan_count
#print axioms every_machine_exact
end AspisV8.CopyTagOffset
