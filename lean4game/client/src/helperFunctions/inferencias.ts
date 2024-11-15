// Esta función caga las vainas si le metes un contador que ya existe, pero ps equis.
export function transformar_input_usuario(input_usuario: string, contador:number): string {
  const words = input_usuario.split(" ")
  if (words[0] == "adicion") {
    return `have s${contador}:${words[1]}∨${words[2]} := by ${input_usuario}\n`
  } else {
    return `have s${contador} := by ${input_usuario}\n`;
  }
}

export function transformar_respuesta_editor(respuesta_editor: string): string {
  let posicion_by = respuesta_editor.indexOf("by")
  return respuesta_editor.slice(posicion_by+3)
}
