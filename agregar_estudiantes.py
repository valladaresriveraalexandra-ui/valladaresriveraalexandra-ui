import sqlite3

# Conectamos a tu base de datos
conexion = sqlite3.connect("rae.db")
cursor = conexion.cursor()

# Datos del estudiante que vas a agregar
nombre_est = "camila"
apellido_est = "campos"
grado_est = "6to"


try:
    # Insertamos en la tabla estudiantes respetando sus columnas
    cursor.execute("""
        INSERT INTO estudiantes (nombre, apellido, grado) 
        VALUES (?, ?, ?)
    """, (nombre_est, apellido_est, grado_est))
    
    # Guardamos los cambios
    conexion.commit()
    print(f"¡Estudiante {nombre_est} agregado con éxito!")

except sqlite3.Error as e:
    print(f"Hubo un error al insertar: {e}")

finally:
    conexion.close()