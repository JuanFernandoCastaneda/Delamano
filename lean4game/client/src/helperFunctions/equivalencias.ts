export function transformar_input_usuario(input_usuario: string): string {
  let [comando, posicion] = input_usuario.split(";")
  let texto = "rw ";
  // Esto pasa si no se especifica la posición, del tipo comando; pos vs comando solo.
  if (posicion != undefined) {
    texto += `(config := {occs := .pos [${parseInt(posicion)}]})`
  }
  texto += "[" + comando.trim() + "]" + "\n"
  return texto
}

export function transformar_respuesta_editor(respuesta_editor: string): string {
  let posicion_primer_corchete_abierto = respuesta_editor.indexOf("[")
  let posicion_primer_corchete_cerrado = respuesta_editor.indexOf("]")
  // EL input es del estilo rw (config := {occs := .pos [2]})[← double_negation p]
  if (respuesta_editor.includes("config")) {
    let posicion_segundo_corchete_abierto = respuesta_editor.indexOf("[", posicion_primer_corchete_abierto+1)
    let posicion_segundo_corchete_cerrado = respuesta_editor.indexOf("]", posicion_primer_corchete_cerrado+1)
    return respuesta_editor.slice(posicion_segundo_corchete_abierto+1, posicion_segundo_corchete_cerrado) + "; " + respuesta_editor.slice(posicion_primer_corchete_abierto+1, posicion_primer_corchete_cerrado)
  // El input del estilo es rw [← double_negation p]
  } else {
    return respuesta_editor.slice(posicion_primer_corchete_abierto+1, posicion_primer_corchete_cerrado)
  }
}

// EJemplo: de_morgan_o (p q : Prop) : ¬(p ∨ q) ↔ ¬p ∧ ¬q
export function extraer_hipotesis_altTitle(altTitle: string): string {
  let posParentesisAbierto = altTitle.indexOf("(")
  let posDosPuntos = altTitle.indexOf(":")
  let hipotesis = altTitle.slice(posParentesisAbierto+1, posDosPuntos).trim().split(" ")
  return hipotesis.map((x) => x+"(Reemplazar variable)").join(" ")
}
