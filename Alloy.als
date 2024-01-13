sig Text {}
sig EncryptedText {}

sig PencariKerja {
  nama: Text,
  username: Text,
  password: EncryptedText,
}

sig LoginService {
  lusername: Text,
  password: EncryptedText
}

sig Lowongan {
  lowongan: Text,
  listOfPendaftars: set ApplicantsForm,
}

sig ApplicantsForm {
  cv: CV,
  suratPengantar: Text,
  referensi: Text,
  kontakDarurat: Int,
  informasiTambahan: Text,
}

sig CV {
  nama: Text,
  pendidikan: Text,
  deskripsiDiri: Text,
  keahlian: Text,
  pengalaman: Text,
  email: Text,
  nomorTelepon: Int,
}

pred nLowongan {
  #Lowongan > 2
}

pred nApplicants {
  #ApplicantsForm > 0
}

pred nCV {
  #CV = 1
}

pred nLogin {
  #LoginService = 1
}

pred PencariKerjaSudahLogin[pk: PencariKerja, ls: LoginService] {
  ls.lusername in pk.username
  ls.password in pk.password
}

pred ApplicantsFormDapatDiakses[af: ApplicantsForm, pk: PencariKerja, ls: LoginService] {
  PencariKerjaSudahLogin[pk, ls]
}

assert LoginSebelumLamar {
  all af: ApplicantsForm, l: Lowongan | 
    (af in l.listOfPendaftars) implies (some pk: PencariKerja, ls: LoginService | ApplicantsFormDapatDiakses[af, pk, ls])
}

fact {
  some K: PencariKerja | K.username != none and K.nama != none and K.password != none
}

fact {
  nLowongan && nApplicants && nCV && nLogin
}

fact nomortelepon {
  all n : CV | n.nomorTelepon > 0
   all d : ApplicantsForm | d. kontakDarurat> 0
}

assert punyaCV {
  all C: ApplicantsForm | C.cv in CV
}

assert punyaPelamar {
  all L: Lowongan | one P: L.listOfPendaftars | P in ApplicantsForm
}

assert lowonganUnique {
  // Nama setiap Lowongan harus unik
  all disj L1, L2, L3: Lowongan | L1.lowongan != L2.lowongan && L1.lowongan != L3.lowongan && L2.lowongan != L3.lowongan
}

run {} for 3 
check punyaCV for 3
check punyaPelamar for 3
check lowonganUnique for 3
check LoginSebelumLamar for 3
