const reg_simple = /^[a-zA-Z_]+$/
const reg_pos = /^[a-zA-Z_]+\spos\s[1-9]+$/
const reg_props = /^[a-zA-Z_]+(\s[a-zA-Z]+)+$/
const reg_modif = /^modificar_hipotesis/

// retorna arreglo de strings.
export function transformar_input_usuario(input_usuario: string, es_equivalencia: boolean) {
  const lista_inputs = input_usuario.split(";")
  const comandos_a_ejecutar = []
  lista_inputs.forEach((value, index) => {
    const input = value.trim()
    if(!reg_simple.test(input) && !reg_pos.test(input) && !reg_props.test(input)) {
      throw new Error("Hay un error en el comando "+ index + ": " + input)
    } else if(reg_modif.test(input) && es_equivalencia) {
      throw new Error("Estás utilizando el comando modificar_hipotesis en una equivalencia")
    }
    comandos_a_ejecutar.push(transformar_input_usuario_2(input))
  })
  return comandos_a_ejecutar
}

function transformar_en_inferencia() {

}

function transformar_en_equivalencia() {

}

export function transformar_input_usuario_2(input_usuario: string): string {
  let texto = "rw ";
  let comando = input_usuario
  if (reg_pos.test(input_usuario)) {
    let palabras = input_usuario.split(" ")
    const posicion = parseInt(palabras[2])
    texto += `(config := {occs := .pos [${posicion}]})`
    palabras.splice(2, 1);
    comando = palabras.join(" ")
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
