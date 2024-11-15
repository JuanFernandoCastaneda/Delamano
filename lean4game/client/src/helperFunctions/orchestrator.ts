import { transformar_input_usuario as tiEq, transformar_respuesta_editor as trEq} from './equivalencias'
import { transformar_input_usuario as tiIn, transformar_respuesta_editor as trIn} from './inferencias'

enum TipoDemostración {
  "Equivalencias",
  "Inferencias",
  "TeoriaNums",
  "InduccionEstruct"
}

export function transformar_input_usuario(input_usuario: string, tipo: string, contadorPaso: number = 1): string {
  switch (tipo) {
    case "Equivalencias": {
      return tiEq(input_usuario);
    }
    case "Inferencias": {
      return tiIn(input_usuario, contadorPaso)
    }
  }
}

export function transformar_respuesta_editor(input_usuario: string, tipo: string): string {
  switch (tipo) {
    case "Equivalencias": {
      return trEq(input_usuario);
    }
    case "Inferencias": {
      return trIn(input_usuario)
    }
  }
}
