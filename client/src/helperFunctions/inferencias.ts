import {transformar_input_usuario as tiEq, transformar_respuesta_editor as trEq } from './equivalencias'

// Esta función caga las vainas si le metes un contador que ya existe, pero ps equis.
export const teoremas = ["modus_ponens", "modus_tollens", "silogismo_disyuntivo", "transitividad", "resolucion", "simplificacion", "conjuncion", "adicion"];
export const tacticas = []

// assumes trimmed
export function transformar_input_usuario(input_usuario: string, contador:number): string {
  const words = input_usuario.split(" ")
  if (words[0] == "sea") {
    if (words[2] == "por") {
      if (teoremas.includes(words[3]) ) {
        return `have s${contador}: ${words[1]} := by ${input_usuario.split("por")[1]}\n`;
      } else {
        // Solo se puede hacer sea con inferencias.
        return "Cuando utilizas la keyword 'sea' solo sirve con reglas de inferencia."
      }
    } else {
      return "Tienes que explicar con la keyword 'por' el procedimiento que usaste."
    }
  } else {
    // EL TIEQ SE ENCARGA DE VERIFICAR QUE SEA UN INPUT VÁLIDO DE EQUIVALENCIA.
    let [comando, hip] = input_usuario.split("en")
    if (hip != undefined) {
      // No dejo espacio porque hip ya tiene un espacio
      return tiEq(comando).slice(0, -1) + " at" + hip + "\n"
    } else {
      return tiEq(input_usuario)
    }
  }
}

export function transformar_respuesta_editor(respuesta_editor: string): string {
  if (respuesta_editor.includes("have")) {
    const primer = respuesta_editor.indexOf(":");
    const segund = respuesta_editor.indexOf(":", primer+1);
    let posicion_by = respuesta_editor.indexOf("by")
    return `sea ${respuesta_editor.slice(primer+2, segund-1)} por ${respuesta_editor.slice(posicion_by+4)}`
  } else {
    let [respuesta, hip] = respuesta_editor.split(" at");
    // No dejo espacio porque hip ya tiene un espacio
    return trEq(respuesta) + (hip != undefined ? ` en${hip}`: "");
  }
}
