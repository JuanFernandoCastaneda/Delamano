import { transformar_input_usuario as tiEq, transformar_respuesta_editor as trEq} from './equivalencias'
import { transformar_input_usuario as tiIn, transformar_respuesta_editor as trIn} from './inferencias'
import { transformar_input_usuario as tiNat, transformar_respuesta_editor as trNat } from './induccionEstructNat'

export const esTacticaDeSoporte = (tactica) => {
  return tactica == "induction" || tactica == "rw" || tactica == "have" || tactica == "config"
}

export function transformar_input_usuario(input_usuario: string, tipo: string, contadorPaso: number = 1): string {
  const separadoPorEspacios = input_usuario.split(" ")
  const espaciosBorrados = separadoPorEspacios.filter((elem) => elem != '')
  input_usuario = espaciosBorrados.join(' ')
  switch (tipo) {
    case "Equivalencias": {
      return tiEq(input_usuario);
    }
    case "Inferencias": {
      return tiIn(input_usuario, contadorPaso)
    }
    case "InduccionEstructNat": {
      return tiNat(input_usuario)
    }
  }
}

export function transformar_respuesta_editor(input_usuario: string, tipo: string): string {
  input_usuario = input_usuario.trim()
  switch (tipo) {
    case "Equivalencias": {
      return trEq(input_usuario);
    }
    case "Inferencias": {
      return trIn(input_usuario)
    }
    case "InduccionEstructNat": {
      return trNat(input_usuario)
    }
  }
}
